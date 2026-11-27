# Variance of the Colless index under the Yule model

**Setting.** For a rooted binary phylogenetic tree $T$ with $n$ leaves, the **Colless index** is

$$C(T)=\sum_{v}\big|\kappa(v_1)-\kappa(v_2)\big|,$$

the sum over internal nodes $v$ of the absolute difference between the numbers of leaves $\kappa(v_1),\kappa(v_2)$ below its two children. Let $C_n=C(T_n)$ with $T_n$ a Yule tree, and $H_m=\sum_{k=1}^m 1/k$, $H_m^{(2)}=\sum_{k=1}^m 1/k^2$ (with $H_0=H_0^{(2)}=0$).

**Theorem (exact Yule variance).** For every $n\ge1$,

$$\sigma_Y^2(C_n)=\frac{5n^2+7n}{2}+(6n+1)\Big\lfloor\frac n2\Big\rfloor-4\Big\lfloor\frac n2\Big\rfloor^2+8\Big\lfloor\frac{n+2}{4}\Big\rfloor^2-8(n+1)\Big\lfloor\frac{n+2}{4}\Big\rfloor-6nH_n$$

$$\qquad+\Big(2\Big\lfloor\frac n2\Big\rfloor-n(n-3)\Big)H_{\lfloor n/2\rfloor}-n^2H^{(2)}_{\lfloor n/2\rfloor}+\Big(n^2+3n-2\Big\lfloor\frac n2\Big\rfloor\Big)H_{\lfloor (n+2)/4\rfloor}-2nH_{\lfloor n/4\rfloor}.$$

**Asymptotics.** Writing $m=\lfloor n/4\rfloor$,

$$\sigma_Y^2(C_n)=-\frac83\big(\pi^2+\log 64-18\big)m^2-2n\log m+\Big(20-8\gamma-32\log 2+\big(24-\tfrac43\pi^2-8\log 2\big)(n\bmod 4)\Big)m+O(1).$$

In particular $\sigma_Y^2(C_n)\sim\big(3-\tfrac{\pi^2}{6}-\log 2\big)n^2$, so the standard deviation of the Colless index grows linearly in $n$, as for the Sackin index.

## Depends on

- [Recursive shape indices and the Yule second-moment recursion](recursive-shape-indices-and-the-yule-second-moment-recursion.md)

## Expansion

The Colless index is recursive with $f_C(a,b)=|a-b|$, so the Yule second-moment recursion applies. Because $|k-(n-k)|$ changes form at $k=n/2$, the sums split at $\lfloor n/2\rfloor$, and evaluating $\sum_k kH_{\lfloor k/2\rfloor}$-type sums produces the floor terms with periods 2 and 4. The quadratic leading coefficient follows from $-\tfrac83(\pi^2+\log64-18)m^2$ with $m\approx n/4$.

## Sources

- Gabriel Cardona, Arnau Mir, Francesc Rosselló, "Exact formulas for the variance of several balance indices under the Yule model", arXiv:1202.6573 (2012). Theorem 4 and Corollaries 7–8, <https://doi.org/10.48550/arXiv.1202.6573>.
