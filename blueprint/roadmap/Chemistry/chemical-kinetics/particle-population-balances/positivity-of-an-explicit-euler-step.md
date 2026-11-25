# Positivity of an explicit Euler step

At a nonnegative state of the finite aggregation-breakage model, write each component as
$n_k' = \mathrm{gain}_k - \mathrm{loss}_k\,n_k$ with $\mathrm{gain}_k, \mathrm{loss}_k \ge 0$ evaluated at that state. The explicit
Euler step $n_k^+ = n_k + \Delta t\,(\mathrm{gain}_k - \mathrm{loss}_k n_k) = (1 - \Delta t\,\mathrm{loss}_k)\,n_k + \Delta t\,\mathrm{gain}_k$
with $\Delta t \ge 0$ is nonnegative whenever $\Delta t\,\mathrm{loss}_k \le 1$ for every $k$. The bound is checked again at each step,
since the loss rates change with the state, and the step conserves mass only with the same mass-balanced gains. A step violating the
bound can make a component negative: $\mathrm{gain} = 1$, $\mathrm{loss} = 2$, $n = 1$ and $\Delta t = 2$ give $n^+ = -1$. Implicit
schemes are outside this result.

## Depends on

- [Mass conservation in a finite aggregation-breakage model](mass-conservation-in-a-finite-aggregation-breakage-model.md)

## Proof depends on

## Sources

- S. Kumar and D. Ramkrishna, On the solution of population balance equations by discretization—I. A fixed pivot technique, *Chemical Engineering Science* 51 (1996) 1311–1332, Sections 3.2–3.4.
