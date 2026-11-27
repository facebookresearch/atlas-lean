# Stationary fitness distribution of the four-species Bak–Sneppen model

**Model.** For $n \ge 3$ species arranged on a cycle, the state is a fitness vector $\mathbf{f}_k = (f_{1,k},\dots,f_{n,k}) \in [0,1]^n$. At each step the index $\nu$ of the minimal fitness is found, and $f_\nu$ together with the fitnesses of its two cyclic neighbours are replaced by independent $\mathrm{Uniform}[0,1]$ variables; the other $n-3$ fitnesses are kept. This is a Markov chain on $[0,1]^n$.

**Qualitative facts.** For every $n$ the chain is uniformly ergodic, so it has a unique stationary distribution $\mu_n$. For $n \ge 4$, started from i.i.d. uniform fitnesses, every finite-time distribution has a piecewise polynomial density with rational coefficients; after one step the density is $\sum_{\nu=1}^n p(\min \mathbf{x}_{]\nu[})$ with $p(x) = x(\tfrac13x^2 - x + 1)$, where $\mathbf{x}_{]\nu[}$ denotes the coordinates other than $\nu$ and its two neighbours.

**Theorem ($n = 4$).** Let

$$
q(x) = \frac32\,\frac{x\,\big(3 - x(3-x)\big)}{\big(3 - x(3 - x(3-x))\big)^2}, \qquad 0 \le x \le 1 .
$$

The stationary distribution of the four-species Bak–Sneppen model is

$$
\mu_4(d^4\mathbf{x}) = \Big[\sum_{\nu=1}^4 q(x_\nu)\Big]\,\mathbf 1_{[0,1]^4}(\mathbf{x})\,d^4\mathbf{x},
$$

and the asymptotic fitness distribution at a fixed site has density

$$
\frac{d}{dx}\,\mathbb{P}(f_{1,\infty} \le x) = \Big(\frac34 + q(x)\Big)\,\mathbf 1_{[0,1]}(x).
$$

For $n = 5$ the stationary density is determined by coefficients satisfying an explicit linear recurrence.

## Expansion

For $n = 4$ only one coordinate survives each step (the one opposite the minimum), so the density after $k$ steps has the form $\sum_\nu q_k(x_\nu)$ with $q_k(x) = \sum_i \alpha_{k,i}x^i$ a polynomial. Applying the transition kernel gives a linear recursion for the coefficients: $\alpha_{k,0} = 0$, $\alpha_{k+1,1} = 2\sum_j \alpha_{k,j}/(j+1)$, and for $i \ge 4$, $\alpha_{k+1,i} = \tfrac{i+1}{i}\alpha_{k,i-1} - \tfrac{i+1}{i-1}\alpha_{k,i-2} + \tfrac13\tfrac{i+1}{i-2}\alpha_{k,i-3}$. Each coefficient stabilizes after finitely many steps ($\alpha_{k,i} = \beta_i$ for $k \ge i+1$), $q_k \to q = \sum_i \beta_i x^i$ uniformly, and summing the generating function of the limiting recursion gives the closed form. Uniform ergodicity identifies the limit with $\mu_4$.

## Sources

- Eckhard Schlemm, "Asymptotic fitness distribution in the Bak-Sneppen model of biological evolution with four species", *Journal of Statistical Physics* 148 (2012), 191–203, <https://doi.org/10.1007/s10955-012-0538-2>; preprint arXiv:1207.0108, <https://doi.org/10.48550/arXiv.1207.0108>. Numbering of the arXiv version: Section 2 (Propositions 1–2), Section 3 (Propositions 3–4, Theorem 1), Section 4 (Proposition 5).
