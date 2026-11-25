# Incentive compatibility (quasi-linear, dominant strategies)

Throughout, $I$ is a finite set of agents and $A$ a set of alternatives; a valuation profile $v = (v_i)_{i \in I}$ gives each agent a valuation $v_i : A \to \mathbb{R}$, and $(w, v_{-i})$ denotes the profile $v$ with $v_i$ replaced by $w$.
A direct mechanism is given by an alternative rule $f$, which maps every reported profile to an
alternative, and a payment rule $p$, which maps a reported profile $v$ and an agent $i$ to a real payment
$p(v, i)$. The mechanism $(f, p)$ is incentive compatible if for every agent $i$, every profile $v$ and every
report $w : A \to \mathbb{R}$ of agent $i$,

$$v_i\bigl(f(w, v_{-i})\bigr) - p\bigl((w, v_{-i}), i\bigr) \le v_i(f(v)) - p(v, i)$$

(Nisan 2007, Definition 9.15): with quasi-linear utilities, reporting the true valuation is a dominant
strategy.

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.15.
