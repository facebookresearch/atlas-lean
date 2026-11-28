# Robust spike-detection threshold and temperature-path cluster selection

**Detection threshold.** Let $x$ be the band-pass filtered (300–3000 Hz) extracellular signal. Spikes are detected where the signal (of the chosen polarity, or $|x|$ for both polarities) crosses

$$\mathrm{Thr} = 5\,\sigma_n, \qquad \sigma_n = \mathrm{median}\Big\{\frac{|x|}{0.6745}\Big\}.$$

If the background is Gaussian noise $\mathcal N(0, \sigma^2)$, then $\mathrm{median}|x| = \Phi^{-1}(3/4)\,\sigma \approx 0.6745\,\sigma$, so $\sigma_n$ is a consistent estimate of $\sigma$. Unlike the sample standard deviation, it is barely affected by the spikes themselves: a fraction $\eta$ of large-amplitude samples moves the median of $|x|$ only to the $\tfrac{1}{2(1-\eta)}$-quantile of $|x|$ under the noise law, whereas the standard deviation grows with the spike amplitude and firing rate (and so would raise the threshold exactly when there are many spikes).

**Features.** Each detected waveform (64 samples) is decomposed by a four-level Haar wavelet transform; coefficients whose distribution across spikes departs most from normality (Lilliefors test, after discarding values beyond three standard deviations) are kept, since multimodal coefficients separate clusters.

**Cluster selection on the temperature path.** Superparamagnetic clustering gives partitions at temperatures $T_0 < T_1 < \dots$; at each $T_n$ let $C^{T_n}_1, C^{T_n}_2, \dots$ be the clusters sorted by decreasing size, with $|C^{T_{-1}}_i| = 0$.

1. *Peak selection.* Select every cluster with

$$|C^{T_n}_i| - |C^{T_{n-1}}_i| \ge N_{\mathrm{inc}},$$

together with all larger clusters $C^{T_n}_j$, $j < i$, of the same partition.
2. *Regime border.* With the largest increment $LI_{T_i} = \max_{j > 1}\big(|C^{T_i}_j| - |C^{T_{i-1}}_j|\big)$, the end of the superparamagnetic regime is

$$T_B = \min\Big\{T_i : \frac{|C^{T_i}_1| + LI_{T_i}}{|C^{T_{i-1}}_1|} < \mathrm{Thr}_{\mathrm{border}}\Big\},$$

and partitions at $T_i \ge T_B$ are discarded (overclustering): the principal cluster has shattered beyond what one new cluster explains.
3. *Inclusion.* With the overlap coefficient

$$O^{T_n, T_m}_{i,j} = \frac{|C^{T_n}_i \cap C^{T_m}_j|}{\min(|C^{T_n}_i|, |C^{T_m}_j|)} \in [0, 1],$$

equal to $1$ iff one cluster contains the other, two selected clusters with $O \ge k_O$ are treated as the same cluster and only the one at the higher temperature is kept.

Remaining waveforms are assigned by template matching to the nearest cluster centroid if their Euclidean distance is below $3\sigma_T$, $\sigma_T^2 = \sum_{i=1}^{64}\mathrm{var}(x_i)$ the cluster's total variance; otherwise they are labelled noise.

## Expansion

For $X \sim \mathcal N(0, \sigma^2)$, $\Pr(|X| \le c\sigma) = 2\Phi(c) - 1 = \tfrac12$ gives $c = \Phi^{-1}(0.75) \approx 0.6745$. If a fraction $\eta$ of samples are spikes with $|x|$ above the noise range, the median of $|x|$ is the point where the noise samples alone account for half of all samples, i.e. the noise quantile of level $\tfrac{1}{2(1 - \eta)}$, which for small $\eta$ is close to the median; this is the robustness property (breakdown point $\tfrac12$ of the median). The threshold $5\sigma_n$ then puts the Gaussian false-crossing probability per sample at about $2\bar\Phi(5) \approx 6 \times 10^{-7}$. The overlap coefficient is the Szymkiewicz–Simpson coefficient; using the minimum in the denominator makes nested clusters (the same cluster appearing at successive temperatures) score $1$. In the source the defaults were $\mathrm{Thr}_{\mathrm{border}} = 0.4$ (results insensitive between $0.25$ and $0.45$) and $k_O = 0.9$, with temperatures $0$ to $0.25$ in steps of $0.01$.

## Sources

- F. J. Chaure, H. G. Rey, R. Quian Quiroga, "A novel and fully automatic spike-sorting implementation with variable number of features", Journal of Neurophysiology (2018), Methods (Eq. (1) detection threshold; wavelet features and Lilliefors selection; superparamagnetic clustering and template matching; Eqs. (2)–(4) peak selection, regime border and inclusion criterion), <https://doi.org/10.1152/jn.00339.2018> (PMC6230803).
