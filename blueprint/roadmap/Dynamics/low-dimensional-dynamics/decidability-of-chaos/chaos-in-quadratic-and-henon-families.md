# Positive Lyapunov exponents and SRB measures in the quadratic and Hénon families are undecidable over the reals

In the Blum–Shub–Smale model of computation over the reals, the sets of parameters for which a quadratic map or a Hénon map has a positive Lyapunov exponent, or an SRB measure, are undecidable, while positivity of topological entropy in the quadratic family is decidable.

Let $Q_a(x) = 1 - a x^2$ ($a, x \in \mathbb{R}$) be the quadratic family and $H_{a,b}(x, y) = (1 - a x^2 + y, b x)$ the Hénon maps.

- The Lyapunov exponent of $Q_a$ is $\lambda(Q_a) = \limsup_{n \to \infty} \frac{1}{n} \log |DQ_a^n(1)|$, and that of $H_{a,b}$ is $\lambda(H_{a,b}) = \limsup_{n\to\infty} \frac{1}{n}\log \|DH_{a,b}^n(z_0)(0,1)\|$ for a critical point $z_0$ in the sense of Benedicks and Carleson.
- An SRB measure for $Q_a$ is an invariant measure absolutely continuous with respect to Lebesgue measure; for $H_{a,b}$ it is an invariant measure with a positive Lyapunov exponent almost everywhere whose conditional measures on unstable manifolds are absolutely continuous with respect to the induced Lebesgue measure.
- For a fixed small $b_0 > 0$ let $\exp^+(Q)$ and $\mathrm{srb}(Q)$ be the sets of $a \in (0, 2]$ for which $Q_a$ has a positive Lyapunov exponent, respectively an SRB measure; let $\exp^+(H)$ and $\mathrm{srb}(H)$ be the corresponding sets of $(a, b) \in (0, 2] \times (-b_0, b_0)$ for $H_{a,b}$; and let $\mathrm{ent}^+(Q)$ be the set of $a \in (0, 2]$ for which $Q_a$ has positive topological entropy.
- Decidability is in the sense of Blum, Shub and Smale for machines over $\mathbb{R}$: a set $S \subseteq \mathbb{R}^n$ is a *halting set* if some such machine halts exactly on the inputs in $S$, and $\Omega \subseteq \mathbb{R}^n$ is *decidable* if $\Omega$ and its complement are halting sets.

**Theorem.** The sets $\exp^+(Q)$, $\exp^+(H)$, $\mathrm{srb}(Q)$ and $\mathrm{srb}(H)$ are undecidable. The set $\mathrm{ent}^+(Q)$ is decidable (Theorem A of the source).

## Depends on

- [Lebesgue measure on the real line](../../../MeasureTheory/lebesgue-measure/lebesgue-measure-on-euclidean-spaces/lebesgue-measure-on-the-real-line/lebesgue-measure.md)
- [Topological entropy of a self-map of a compact space](../../topological-symbolic-dynamics/topological-entropy/topological-entropy.md)

## Proof depends on

None.

## Expansion

Decidability here refers to Blum–Shub–Smale machines over $\mathbb R$ (register machines with exact real arithmetic and comparisons, as described above), a model with no definition page on main yet.

By a theorem of Blum, Shub and Smale, every halting set over $\mathbb{R}$ is a countable union of basic semi-algebraic sets, so it has countably many connected components, and so does every decidable set. By Benedicks and Carleson, $\exp^+(Q)$ has positive Lebesgue measure; a map $Q_a$ with a positive Lyapunov exponent has no attracting periodic orbit, while by Graczyk–Świątek and Lyubich the parameters with an attracting cycle form an open dense set, so $\exp^+(Q)$ has empty interior. A set of positive measure with empty interior has uncountably many connected components, hence $\exp^+(Q)$ is not decidable. A machine deciding $\exp^+(H)$ would decide $\exp^+(Q)$ by restricting to $b = 0$, where $H_{a,0}(x, 0) = (Q_a(x), 0)$. The same argument applies to $\mathrm{srb}(Q)$, which has positive measure by Jakobson's theorem and empty interior since an absolutely continuous invariant measure excludes an attracting cycle, and then to $\mathrm{srb}(H)$. Finally $a \mapsto h_{\mathrm{top}}(Q_a)$ is monotone, so $\mathrm{ent}^+(Q)$ is an interval, and intervals are decidable. The question was raised by Carleson and by Smale; the decidability of positive topological entropy for Hénon maps is left open.

## Sources

- A. Arbieto and C. Matheus, "Decidability of chaos for some families of dynamical systems", Foundations of Computational Mathematics 4 (2004), no. 3, https://doi.org/10.1007/s10208-003-0085-y; read in arXiv:math/0212101v2 (Theorem A in the introduction, the definitions and Proposition 2.5 in Section 2, and the proof of Theorem A in Section 3 of arXiv:math/0212101v2).
