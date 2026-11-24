# Local martingales and localization

Let $(\mathcal F_t)_{t\ge0}$ be a right-continuous filtration on a probability space. A localizing sequence is a nondecreasing sequence of stopping times $(\tau_n)$ with $\tau_n\to\infty$ almost surely. An adapted process $M$ with right-continuous paths is a local martingale if there is a localizing sequence such that every stopped process $M^{\tau_n}_t=M_{t\wedge\tau_n}$ is an $(\mathcal F_t)$-martingale; it is a continuous local martingale if moreover its paths are continuous. More generally, a property of processes holds locally if it holds for the stopped processes along some localizing sequence.

Two basic consequences belong to the definition:

- a continuous local martingale $M$ with $|M_t|\le K$ for all $t$ is a martingale, by dominated convergence of $\mathbb E[M_{t\wedge\tau_n}\mid\mathcal F_s]=M_{s\wedge\tau_n}$;
- a local martingale with $M_t\ge0$ for all $t$ is a supermartingale, by Fatou's lemma for conditional expectations.

Some sources instead require $M^{\tau_n}-M_0$, or $M^{\tau_n}\mathbf 1_{\{\tau_n>0\}}$, to be a (uniformly integrable) martingale; the versions differ only in integrability of $M_0$.

## Proof depends on

- [Optional stopping theorem in continuous time](../optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)

## Expansion

A full page defines the localization operator on properties of processes, proves that a stopped martingale is a martingale (via [optional stopping in continuous time](../optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)), that localizing sequences can be combined by taking minima, and the two consequences above, and that for a continuous local martingale the times $\inf\{t:|M_t|\ge n\}$ form a localizing sequence when $M_0$ is bounded.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren 293, Springer, 1999, <https://link.springer.com/book/10.1007/978-3-662-06400-9>, local martingales chapter (topic).
