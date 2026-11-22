# Sanov's upper bound, non-asymptotic

Let $Q \ge 0$ on a finite alphabet $\alpha$, let $\Gamma$ be any set of functions $\alpha \to \mathbb R$, and
let $r$ satisfy $r \le D(P \| Q) = \sum_a P(a)\log(P(a)/Q(a))$ for every probability vector
$P \in \Gamma$ with $Q(a) > 0$ wherever $P(a) > 0$. Then for $n \ge 1$, with the natural logarithm,

$$Q^n\{x : P_x \in \Gamma\} \le (n+1)^{|\alpha|}\, e^{-nr}.$$

The hypothesis on $r$ says $r \le D(\Gamma \| Q) = \inf_{P} D(P\|Q)$, the infimum over the
distributions $P \in \Gamma$ (only empirical distributions matter, so other elements of $\Gamma$ are
ignored), with the source's convention $D = +\infty$ when $P \not\ll Q$; passing $r$ instead of the infimum avoids an infimum of
extended-real divergences. No topological hypothesis on $\Gamma$ is needed.
Csiszár's (III.25) has the sharper exponent $D(\Gamma \cap \mathcal P_n \| Q)$ and the factor
$|\mathcal P_n|$; the form here is what (III.20) uses.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, (III.25) and Lemma II.1.
