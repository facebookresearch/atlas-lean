# Positive recurrence of weakly reversible stochastic mass-action networks

**Setting.** A finite reaction network has complexes $y\in\mathbb Z^d_{\ge0}$ and reactions $y\to y'$. Under stochastic mass-action kinetics the molecule counts $X(t)\in\mathbb Z^d_{\ge0}$ form a continuous-time Markov chain in which reaction $y\to y'$ fires at rate
$$\lambda_{y\to y'}(x)=\kappa_{y\to y'}\prod_{i=1}^d\frac{x_i!}{(x_i-y_i)!}\,\mathbf 1\{x\ge y\},\qquad\kappa_{y\to y'}>0,$$
and moves the state by $y'-y$. Let $X$ be the minimal chain. The network is *weakly reversible* if every reaction $y\to y'$ lies on a directed cycle of reactions, i.e. there is a directed path of complexes from $y'$ back to $y$.

**Theorem 3.1.** If the network is weakly reversible and every rate constant is positive, then the minimal chain is non-explosive from every initial population, every communicating class is closed, and the chain restricted to each communicating class is positive recurrent; in particular each class carries a unique stationary distribution.

**Proposition 3.2 (Foster–Lyapunov criterion).** Let $X$ be an irreducible minimal chain on a countable set $\Gamma$ with finitely many transitions out of each state and generator $Q$. If $V:\Gamma\to[1,\infty)$ has finite sublevel sets and $QV\le -c$ outside a finite set for some $c>0$, then $X$ is non-explosive and positive recurrent. The proof constructs a global weight $V$ satisfying $QV(n)\le-q(n)$ outside a finite subset of each infinite class (Proposition 7.2).

## Depends on

- [Non-explosivity of complex-balanced stochastic reaction networks](non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)

## Expansion

Closedness of classes is combinatorial: if $y\to y'$ fires from $y+w$, weak reversibility gives a path of complexes $y'\to\dots\to y$, and leaving the same $w$ molecules aside at each step returns the chain to $y+w$, so every transition can be undone. Finite classes are then trivially positive recurrent. For an infinite class the difficulty is that no single linear or entropy-like function decreases in every direction of escape. The proof assembles a weight from exponentials of weighted populations $a\cdot x$ over finitely many slopes $a\in[0,1]^d$, corrected by penalties selected at a common scale (Proposition 6.2), and controls the order in which species can grow along excursions (the return-height theorem, Theorem 4.9). This removes the complex-balance hypothesis needed by earlier results, where the product-form Poisson stationary distribution gives positive recurrence directly; weak reversibility alone does not provide an explicit stationary law.

## Sources

- D. Cappelletti, G. Cuniberti, "Positive recurrence of weakly reversible stochastic reaction networks with mass-action kinetics", arXiv preprint (2026), Theorem 3.1, Proposition 3.2, Theorem 4.9, Proposition 6.2 and Proposition 7.2, <https://doi.org/10.48550/arXiv.2611.32819>.
