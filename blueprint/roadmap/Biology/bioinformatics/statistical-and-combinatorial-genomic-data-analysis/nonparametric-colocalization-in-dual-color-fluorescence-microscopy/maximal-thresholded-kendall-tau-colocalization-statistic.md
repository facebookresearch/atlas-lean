# Maximal thresholded Kendall tau colocalization statistic

**Setting.** A dual-color fluorescence image (or region of interest) gives intensity pairs $(X_i, Y_i)$, $i\in\mathcal{I}$, $n = |\mathcal{I}|$, for two labelled molecules. Pearson's coefficient $r$ measures only linear dependence, and Manders' split coefficients $M_1 = \sum_{i:Y_i>\alpha_Y}X_i/\sum_iX_i$, $M_2 = \sum_{i:X_i>\alpha_X}Y_i/\sum_iY_i$ are linear measures between one channel and a thresholded indicator of the other. Both depend on monotone rescalings of intensity: for $(\log X,\log Y)$ bivariate normal with variance $9$ and correlation $0.9$, the Pearson correlation of $(X,Y)$ is only $(e^{8.1}-1)/(e^{9}-1) \approx 0.41$.

**Thresholded Kendall tau.** For thresholds $t_X, t_Y$ let $\mathcal{K}(t_X,t_Y) = \{i : X_i\ge t_X,\ Y_i\ge t_Y\}$, $n_{t} = |\mathcal{K}(t_X,t_Y)|$, and

$$\tau(t_X,t_Y) = \frac{1}{n_t(n_t-1)}\sum_{i\neq j\in\mathcal{K}(t_X,t_Y)}\operatorname{sign}(X_i-X_j)\operatorname{sign}(Y_i-Y_j)$$

($-\infty$ if $n_t\le1$). Under independence $\operatorname{Var}\tau(t_X,t_Y) = \frac{2(2n_t+5)}{9n_t(n_t-1)}$, so the **colocalization statistic** is the maximal standardized value over signal-level thresholds,

$$\tau^* = \max_{t_X\ge X_{(\lfloor n/2\rfloor)},\ t_Y\ge Y_{(\lfloor n/2\rfloor)}}\ \tau(t_X,t_Y)\sqrt{\frac{9n_t(n_t-1)}{2(2n_t+5)}},$$

where $X_{(k)}$ is the $k$th order statistic (the median lower bounds can be replaced by rough background thresholds).

**Properties.** $\tau^*$ depends on the data only through ranks, so it is invariant under arbitrary increasing transformations of either channel, and it ignores pixels where either channel is background. The maximum is attained on thresholds at order statistics, $O(n^2)$ pairs, each needing $O(n\log n)$ for Kendall's tau, i.e. $O(n^3\log n)$ in total. Restricting $t_X = X_{(j)}$, $t_Y = Y_{(k)}$ to $j,k\in\mathcal{R}_n = \{\lfloor n - (1+1/\log\log n)^m\rfloor : m\in\mathbb{N}_+\}\cap[\lfloor n/2\rfloor, n]$, a nearly geometric grid, gives $\tau^*_{\rm app}$.

## Proof sketch

Pearson and Manders coefficients are linear statistics of particular monotone transforms of the intensities, so the natural robust generalization is a rank correlation invariant to all monotone transforms; Kendall's tau is chosen because its null variance is explicit. Restricting to bright pixels on both channels targets dependence among signal pixels, and scanning over unknown signal thresholds with a variance-standardized statistic is a scan-statistic construction. The geometric grid works because neighbouring threshold pairs give highly correlated standardized statistics, so a grid with ratio $1 + 1/\log\log n$ loses only a negligible fraction of the maximum.

In the source, $\tau^*_{\rm app}$ is computed at nearly linear cost and reported to have the same detection power as $\tau^*$. For testing, under $H_0$ (independent channels), the null law of $\tau^*$ is estimated by recomputing it after block-wise random shuffling of one channel, with block size set by the point spread function to preserve within-channel spatial dependence; the p-value is the fraction of shuffled values exceeding the observed one.

## Sources

- Shulei Wang, Ellen T. Arena, Kevin W. Eliceiri and Ming Yuan, "Automated and Robust Quantification of Colocalization in Dual-Color Fluorescence Microscopy: A Nonparametric Statistical Approach", *IEEE Transactions on Image Processing* 27 (2018), 622–636, <https://doi.org/10.1109/tip.2017.2763821>. Preprint version: arXiv:1710.00965 (2017), Sections 2 and 3.2 (definition of $\tau^*$, the fast approximation $\tau^*_{\rm app}$, Algorithm 1), <https://doi.org/10.48550/arXiv.1710.00965>.
