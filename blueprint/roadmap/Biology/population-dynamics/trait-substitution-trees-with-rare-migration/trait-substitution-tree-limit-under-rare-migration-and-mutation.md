# Trait substitution tree limit under rare migration and rarer mutation

**Model.** A population on a trait space $\mathcal X$ is described by the rescaled measure $X^K_t=\frac1K\sum_i\delta_{x_i}$. An individual with trait $x$ gives birth (clonally) at rate $b(x)$ and dies at rate $d(x)+\int\alpha(x,y)X^K_t(dy)$ (logistic competition). With rate $\epsilon$ an individual at $x$ migrates (moves) to another currently occupied trait site $y$ chosen by a kernel $m(x,dy)$, and with rate $\sigma\mu(x)$ it produces a mutant offspring at $x+h$, $h\sim p(x,dh)$. Write $\bar n(x)=(b(x)-d(x))/\alpha(x,x)$ for the monomorphic equilibrium and $\bar f(y,x)=b(y)-d(y)-\alpha(y,x)\bar n(x)$ for the invasion fitness of $y$ in an $x$-population. Assume the fitness order is total and transitive ($x\prec y$ iff $\bar f(x,y)<0<\bar f(y,x)$), and that competition and migration act only between nearest neighbors in this order.

**Theorem (finite trait space, migration time scale).** Let $\mathcal X=\{x_0\prec x_1\prec\dots\prec x_L\}$, without mutation, start from $X^K_0=\frac{N^K_0}{K}\delta_{x_0}$ with $N^K_0/K\to n_0>0$, and let migration be rare but not too rare:

$$1\ll K\epsilon\ll K.$$

Then (under a growth-rate condition ensuring sequential invasion) there is $\bar t_L>0$ such that for every $t>\bar t_L$, $X^K_{t\ln(1/\epsilon)}$ converges in law, in total variation, to the alternating configuration

$$\Gamma^{(L)}=\sum_{0\le i\le L,\ i\equiv L\ (\mathrm{mod}\ 2)}\bar n(x_i)\,\delta_{x_i},$$

i.e. the fittest trait and every second trait below it persist at their monomorphic equilibria, while the traits in between are suppressed by their fitter neighbor. Fixation happens on the time scale $\ln(1/\epsilon)$; a trait that was outcompeted earlier can be recovered once its competitor is in turn suppressed.

**Theorem (trait substitution tree).** With mutation, start from $X_0=\frac{N^K_0}{K}\delta_{x_0}$, $N^K_0/K\to\bar n(x_0)$, assume $1\ll K\epsilon\ll K$ and

$$\ln\frac1\epsilon\ll\frac1{K\sigma}\ll e^{CK}\quad\text{for every }C>0.$$

Then $(X^{K,\epsilon,\sigma}_{t/(K\sigma)})_{t\ge0}$ converges in finite-dimensional distributions to the **trait substitution tree** $(\Gamma_t)$: a Markov jump process on alternating configurations $\Gamma^{(n)}$ which, from a configuration with occupied traits $z$, jumps at rate $\bar n(z)\mu(z)p(z,dh)$; the mutant $z+h$ is inserted at its place in the fitness order and the configuration is recomputed below it by the alternating rule (the mutant and every second trait under it, down to the next unchanged level), relabeling the traits above.

## Depends on

- [Classification of adaptive-dynamics singular strategies](../classification-of-adaptive-dynamics-singular-str/README.md)

## Expansion

On a finite trait space the dynamics proceed by successive invasions. Migration seeds the next fitter site at density of order $\epsilon$ in time $O(1)$; the seeded subpopulation grows exponentially at rate $\bar f(x_{i+1},x_i)$ and takes time $\frac{1}{\bar f(x_{i+1},x_i)}\ln\frac1\epsilon$ to reach macroscopic size, after which a two-type Lotka–Volterra system switches the dominant type in time $O(1)$. The displaced type decays exponentially but is held at density at least of order $\epsilon$ by migration from its fitter neighbor; once that neighbor is suppressed by the next invader, the displaced type is released from competition and regrows, again on the $\ln(1/\epsilon)$ scale. Induction on $L$ yields the alternating configuration and the bound on $\bar t_L$. With mutation, the condition $\ln(1/\epsilon)\ll 1/(K\sigma)$ makes each reconfiguration instantaneous on the mutation time scale, while $1/(K\sigma)\ll e^{CK}$ prevents large-deviation extinctions; the waiting time to the next mutant is asymptotically exponential with rate $\sum_z\bar n(z)\mu(z)$, as in Champagnat's derivation of the trait substitution sequence. The construction resembles a look-down: a new mutant changes the configuration only below its own level.

## Sources

- Anton Bovier, Shi-Dong Wang, "Multi-time scales in adaptive dynamics: microscopic interpretation of a trait substitution tree model", arXiv (2012). Section 2 (microscopic model), Section 3 (Theorem 3.3, condition $1\ll K\epsilon\ll K$), Section 4 (assumption (C), Definition 4.1 and Theorem 4.3), Section 6 (Proposition 6.1, Lemmas 6.2 and 6.3). <https://doi.org/10.48550/arXiv.1207.4690>
