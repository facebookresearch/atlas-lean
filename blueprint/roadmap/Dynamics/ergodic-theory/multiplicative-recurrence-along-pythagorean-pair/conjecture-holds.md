# Multiplicative recurrence along Pythagorean pairs

Let $(X, \mu)$ be a probability space
and let $(T_a)_{a \ge 1}$, indexed by the positive integers, be measurable bijections of $X$ with
measurable inverses that preserve $\mu$, such that $T_1$ is the identity and
$T_{ab} = T_a \circ T_b$ for all positive integers $a, b$. Then for every measurable set
$A \subseteq X$ with $\mu(A) > 0$ there exist positive integers $m > n$ such that

$$\mu\bigl(T_{2mn}(A) \cap T_{(m-n)(m+n)}(A)\bigr) > 0.$$

This answers the [Pythagorean-pair recurrence problem](conjecture.md) positively. Frantzikinakis, Klurman and Moreira
prove it as Theorem 2.1(i) with coefficients $1$ and $2$: applied to the action $a \mapsto T_a^{-1}$, whose preimages
are the images under $T_a$, it gives the two images above.

## Sources

- Nikos Frantzikinakis, Oleksiy Klurman and Joel Moreira, *Partition regularity of Pythagorean pairs*, Forum Math. Pi 13
  (2025), e5, DOI 10.1017/fmp.2024.27; arXiv:2309.10636, Theorem 2.1(i), <https://arxiv.org/abs/2309.10636>.
