# Revelation principle (dominant strategies)

Let $I$ be a set of agents; agent $i$ has a set $\Theta_i$ of types and a set $X_i$ of actions, and $O$ is a set of outcomes. A mechanism is a map $g : \prod_i X_i \to O$; a direct mechanism is a map $f : \prod_i \Theta_i \to O$. For a profile $x$ and $a \in X_i$, $(a, x_{-i})$ is $x$ with its $i$-th entry replaced by $a$.
Let $u_i(\theta_i, o)$ be private-value utilities. If the strategies $s$ form a profile of dominant
strategies in the mechanism $g$, then the direct mechanism $\theta \mapsto g\bigl((s_j(\theta_j))_{j}\bigr)$
is dominant-strategy incentive compatible; by construction its truthful outcome at every type profile is
the equilibrium outcome of $g$ (Nisan 2007, Proposition 9.25; payments are part of the outcome, so they
agree as well).

## Background

- [Dominant-strategy profile](is-dominant-strategy-profile.md): the hypothesis, applied at the action profile the strategies prescribe.
- [Dominant-strategy incentive compatibility](is-dominant-strategy-incentive-compatibl.md): the conclusion.
- [Gibbard–Satterthwaite theorem](../../social-choice/gibbard-satterthwaite-theorem/README.md): without money and with unrestricted strict preferences, the only onto strategy-proof direct mechanisms over three or more alternatives are dictatorial.

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.24 and Proposition 9.25.
