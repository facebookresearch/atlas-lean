# Asynchronous iteration of sup-norm contractions

In the [totally asynchronous iteration model](the-totally-asynchronous-iteration-model.md), let the vectors be bounded and real, with a weighted sup-norm $\|x\| = \sup_i \alpha_i |x_i|$ where $\underline\alpha \le \alpha_i \le \bar\alpha$ for some $0 < \underline\alpha \le \bar\alpha$, and let $X$ be the whole space or a closed ball around a fixed point $x^*$. If $f$ is a contraction for this norm, $\|f(x) - f(y)\| \le \rho\|x - y\|$ with $\rho < 1$, then $x^*$ is the unique fixed point in $X$ and the sets $X^k = \{x : \|x - x^*\| \le \rho^k q\}$, for any $q > 0$ with $X^0 \subseteq X$, satisfy the conditions of the [asynchronous convergence theorem](the-asynchronous-convergence-theorem.md). Hence the asynchronous iteration converges to $x^*$ from every initial state in $X^0$. The same holds for $P$-contractions $|f(x) - f(y)| \le P|x - y|$ with $P$ nonnegative of spectral radius less than $1$, which are contractions for some weighted sup-norm. A contraction for another kind of norm need not satisfy the conditions.

## Depends on

- [The asynchronous convergence theorem](the-asynchronous-convergence-theorem.md)

## Sources

- D. P. Bertsekas, "Distributed asynchronous computation of fixed points", *Mathematical Programming* 27:107–120, 1983; <https://web.mit.edu/dimitrib/OldFiles/www/Distr_Comp_Fixed.pdf>, Sections 4.1 (contraction mappings with respect to sup-norms) and 4.2 ($P$-contraction mappings).
