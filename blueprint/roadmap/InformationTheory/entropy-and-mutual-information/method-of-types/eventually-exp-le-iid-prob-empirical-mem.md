# Sanov's lower bound, asymptotic form

Let $Q \ge 0$ be a function on the finite alphabet, $\Gamma$ a set of functions on it, $s_n$ an $n$-type for each $n$,
and suppose that for all large $n$ it lies in $\Gamma$ with
$Q(a) > 0$ wherever its empirical distribution is positive, and that $D(P_{s_n} \| Q) \to r$. Then for
every $\varepsilon > 0$, eventually $e^{-n(r+\varepsilon)} \le Q^n\{x : P_x \in \Gamma\}$.

With $r = D(\Gamma \| Q) < \infty$, the existence of such $s_n$ is equivalent to Csiszár's condition
(III.21), $D(\Gamma \cap \mathcal P_n \| Q) \to D(\Gamma \| Q)$, as explained on
[Sanov's theorem for finite alphabets](sanov-theorem-for-finite-alphabets.md).

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Theorem III.3, proof of (III.22).
