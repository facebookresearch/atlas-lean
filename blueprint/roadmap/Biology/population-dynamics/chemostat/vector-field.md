# The chemostat vector field

Let $\mu : \mathbb{R} \to \mathbb{R}$ be a specific growth rate and let the dilution rate $D$, the feed substrate
concentration $S_f$ and the yield $y$ be real. At a state $(X, S) \in \mathbb{R}^2$, with biomass $X$ and
substrate $S$, the chemostat vector field is

$$F(X, S) = \Bigl(\bigl(\mu(S) - D\bigr) X,\; D (S_f - S) - \frac{1}{y}\, \mu(S)\, X\Bigr),$$

a quotient by $0$ being read as $0$. Its integral curves are the solutions of the chemostat balances
$X' = (\mu(S) - D) X$, $S' = D (S_f - S) - \mu(S) X / y$. Monod growth is the
[Michaelis–Menten rate law](../../systems-biology/michaelis-menten-kinetics-and-the-quasi-steady-s/mm-rate.md)
$\mu(S) = \mu_m S / (K_s + S)$.
