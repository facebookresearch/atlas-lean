# Independence of genus ages and sizes in the Yule model

**Yule's model.** Species within a genus multiply as a pure-birth (Yule) process $(Y_t)$ with rate $s$ started from one species, and each genus independently founds new genera at rate $g$; the number of genera $(N_t)$ is a Yule process with rate $g$ started from one genus. A newly founded (daughter) genus starts with one species; the mother genus is unaffected.

**Theorem (ages and sizes).** At time $T$, the pairs $(A_i, S_i)$, $1 \le i \le N_T - 1$, of ages and species numbers of the derived genera are independent and identically distributed as a pair $(A, S)$ killed at the first value of $A$ exceeding $T$, where $A \sim \mathrm{Exp}(g)$ and $\mathbb P(S = k \mid A = a) = \mathbb P(Y_a = k)$. Hence

$$\mathbb P(S = k,\ A \in da) = g e^{-(g+s)a}\big(1 - e^{-sa}\big)^{k-1}\,da, \qquad a > 0,\ k \ge 1,$$

and $N_T$ is geometric with success probability $e^{-gT}$. As $T \to \infty$ the size frequency distribution is the **Yule–Simon law** $\mathbb P(S = k) = \int_0^\infty ge^{-ga}e^{-sa}(1 - e^{-sa})^{k-1}da$, with a power-law tail of exponent $1 + g/s$.

**Theorem (general diversification, sampled genera).** If within-genus diversification $Z$ is a general process with extinction, genera have a lifetime $L$ (the extinction time of $Z$), generic births occur at rate $g$ with $g\mathbb E[L] > 1$, and extant genera are sampled independently with probability $f$, then the coalescence times, ages and sizes $(H_i, A_i, S_i)$ of the sampled genera form an i.i.d. sequence distributed as a triple $(H, A, S)$ and killed at the first $H_i > T$ (a coalescent point process). Let $v$ be the density of $L$, let $\eta \in (0, g)$ be the Malthusian parameter, the root of $\psi(\eta) = 0$ with $\psi(x) = x - g + g\int_0^\infty e^{-xt}v(t)\,dt$, let $W$ be the unique increasing solution with $W(0) = 1$ of $W'(t) = g\big(W(t) - \int_0^t W(s)v(t-s)\,ds\big)$, and let $W_f = 1 - f + fW$. Then $H$ and $S$ are independent conditionally on $A$, and

$$\mathbb P(A \in da) = g e^{-\eta a}\,\mathbb P(L > a)\,da, \qquad \mathbb P(H < h,\ A \in da) = \frac{f\,W(h - a)}{W_f(h)}\,g\,\mathbb P(L > a)\,da \quad (0 < a \le h),$$

$$\mathbb P(H = A \in da) = \frac{f}{W_f(a)}\,g\,\mathbb P(L > a)\,da, \qquad \mathbb P(S = k \mid A = a) = \mathbb P(Z_a = k \mid Z_a \ne 0), \qquad \mathbb P(S = k,\ A \in da) = g\,\mathbb P(Z_a = k)\,e^{-\eta a}\,da .$$

**Proposition (birth–death within genera).** If $Z$ is linear birth–death with rates $\lambda, \mu$ and $r = \lambda - \mu$, let $\eta$ be the Malthusian parameter of the generation process and $F(t) = 1 + \lambda(e^{rt} - 1)/r$ ($F(t) = 1 + \lambda t$ if $r = 0$). Then

$$\mathbb P(S = n) = \frac{g}{\lambda}\int_0^\infty e^{-\eta t}\frac{F'(t)}{F(t)^2}\Big(1 - \frac{1}{F(t)}\Big)^{n-1}dt .$$

If $\lambda > \mu$, $S$ has a power-law tail, $\ln\mathbb P(S = n)/\ln n \to -1 - \eta/r$; if $\lambda = \mu$, $\ln\mathbb P(S = n)/\sqrt n \to -2\sqrt{\eta/\lambda}$ (heavy but not power-law); if $\lambda < \mu$ the tail is geometrically light, bounded by a multiple of $(\lambda/\mu)^n/n$.

**Proposition (pure birth with state-dependent rates).** If $Z$ jumps from $k$ to $k+1$ at rate $\lambda_k$, then

$$\mathbb P(S = n) = \frac{g}{g + \lambda_n}\prod_{k=1}^{n-1}\frac{\lambda_k}{g + \lambda_k}, \qquad \mathbb E[A \mid S = n] = \sum_{k=1}^n \frac{1}{g + \lambda_k},$$

and the following are sufficient conditions for the tail behaviour of $S$: if $(\lambda_n)$ is bounded, the tail decays rapidly; if $\ln\lambda_n/\ln n \to c \in (0,1)$, it is heavy but not a power law; if $\ln\lambda_n/\ln n \to c > 1$, one genus blows up in finite time and holds a proportion of all species tending to $1$; if $\lambda_n/n \to s \in (0,\infty)$ (asymptotically linear preferential attachment), $\ln\mathbb P(S = n)/\ln n \to -1 - g/s$. These regimes do not cover every rate sequence: for $\lambda_n = sn$ ($n$ odd) and $\lambda_n = 2sn$ ($n$ even), $\ln\mathbb P(S = n) = -(1 + \tfrac{3g}{4s})\ln n + O(1)$ is a power law although $\lambda_n/n$ has no limit. Analogous regimes appear in urn schemes with preferential attachment.

## Proof sketch

Reading the genealogy of genera backward from time $T$, the founding times of extant derived genera are the atoms of a Poisson-like point process, and conditioning on a founding time $T - a$ the genus has evolved for time $a$ independently of everything else, so its size is $Y_a$; the independence of the pairs is the key structural fact behind Yule's 1925 frequency formula. With extinction, the reconstructed tree of sampled genera is a coalescent point process with i.i.d. node depths $H_i$, which carries the independence to the general case. The tail of $S$ is governed by the competition between the exponential growth rate $\eta$ of the number of genera and the growth rate $r$ of genus size: the ratio $\eta/r$ is the power-law exponent.

## Sources

- Amaury Lambert, "Ages, sizes and (trees within) trees of taxa and of urns, from Yule to today", *Philosophical Transactions of the Royal Society B: Biological Sciences* 380 (2025), 20230305, <https://doi.org/10.1098/rstb.2023.0305>. Preprint version: arXiv:2409.14536 (2024), Theorems 3.1–3.2 (with eqs. (14)–(19)), Propositions 3.1–3.2 and Remark 3.9 (Section 3), <https://doi.org/10.48550/arXiv.2409.14536>.
