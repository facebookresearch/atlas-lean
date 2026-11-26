# Le Cam's bound in KL form

Let $p$ and $q$ be probability mass functions on a finite set $\alpha$ with $p(a) = 0$ wherever $q(a) = 0$, so that the Kullback–Leibler divergence $\mathrm{KL}(p \,\|\, q)$ is finite. For every test $\delta : \alpha \to \{\text{choose } q, \text{choose } p\}$, the two error probabilities satisfy $p(\delta \text{ chooses } q) + q(\delta \text{ chooses } p) \ge 1 - \sqrt{\mathrm{KL}(p \,\|\, q)/2}$. This is Le Cam's two-point bound combined with Pinsker's inequality.
