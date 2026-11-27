# Blumer-Ehrenfeucht-Haussler-Warmuth upper bound for consistent learners

Let $C$ be a class of functions $X \to \{0,1\}$ on a countable domain with measurable singletons, all of whose finite shattered sets have at most $d$ points, let $D$ be a distribution on $X \times \{0,1\}$ realizable by $C$, and let $A$ be any consistent learner for $C$. If $\varepsilon m \ge 8$, then $D^m(\mathrm{err}_D(A(S)) > \varepsilon) \le 2\,\Pi_C(2m)\,2^{-\lceil \varepsilon m/2 \rceil}$. Hence for $\varepsilon, \delta \in (0,1)$ every consistent learner, in particular every empirical risk minimizer, is an $(\varepsilon, \delta)$-PAC learner over the distributions realizable by $C$ from

$$
m \ge \frac{8}{\varepsilon}\Big(d \ln\frac{48}{\varepsilon} + \ln\frac{4}{\delta}\Big)
$$

examples, so the realizable sample complexity is $O((d\ln(1/\varepsilon) + \ln(1/\delta))/\varepsilon)$.

## Proof sketch

Apply the epsilon-net theorem to the loss class $\{(x,y) \mapsto [h(x) \ne y] : h \in C\}$ under $D$, whose growth function is at most that of $C$. On a realizable sample a consistent learner outputs, almost surely, a hypothesis with no sample errors; if its error exceeds $\varepsilon$, its loss indicator is a heavy event missed by the sample.

## Depends on

- [The realizable distribution family](../../occam-bound-for-consistent-learners/realizable-family.md)
- [A consistent learner for a finite class](../../occam-bound-for-consistent-learners/consistent-learner.md)
- [The fundamental theorem of PAC learning](../../is-paclearnable-realizable-family-iff-ha.md)

## Proof depends on

- [The epsilon-net theorem](epsilon-net-theorem.md)

## Sources

- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, "Learnability and the Vapnik-Chervonenkis Dimension", Journal of the ACM, 1989.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
