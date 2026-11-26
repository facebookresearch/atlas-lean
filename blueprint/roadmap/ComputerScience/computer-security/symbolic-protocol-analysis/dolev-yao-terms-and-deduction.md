# Dolev–Yao terms and intruder deduction

Given a set $\mathcal N$ of names (atomic data such as keys, nonces and identities) and a set $\mathcal X$ of variables, the terms $T(\mathcal F, \mathcal X, \mathcal N)$ over the
signature $\mathcal F_{\mathrm{std}} = \{\mathrm{senc}, \mathrm{aenc}, \mathrm{pair}, \mathrm{pk}\}$ are built inductively from names and variables by symmetric encryption
$\mathrm{senc}(t_1, t_2)$, asymmetric encryption $\mathrm{aenc}(t_1, t_2)$, pairing $\langle t_1, t_2\rangle = \mathrm{pair}(t_1, t_2)$ and the public key $\mathrm{pk}(t)$ of a private key $t$;
$\mathrm{st}(t)$ is the set of subterms of $t$. An *inference rule* $\frac{u_1 \cdots u_n}{u}$ relates terms with variables, and an inference system is a set of rules.
The *Dolev–Yao inference system* $\mathcal I_{\mathrm{DY}}$ has the composition rules

$$\frac{x \quad y}{\langle x, y\rangle} \qquad \frac{x \quad y}{\mathrm{senc}(x, y)} \qquad \frac{x \quad y}{\mathrm{aenc}(x, y)}$$

and the decomposition rules

$$\frac{\langle x, y\rangle}{x} \qquad \frac{\langle x, y\rangle}{y} \qquad \frac{\mathrm{senc}(x, y) \quad y}{x} \qquad \frac{\mathrm{aenc}(x, \mathrm{pk}(y)) \quad y}{x}.$$

A term $t$ is *deducible* from a set of terms $S$ in an inference system $\mathcal I$, written $S \vdash_{\mathcal I} t$, if there is a proof tree whose leaves are labelled
by terms of $S$, whose root is labelled by $t$ and each of whose nodes, with its children, is an instance of a rule of $\mathcal I$. The *intruder deduction problem*
for $\mathcal I$ asks, given a finite set of terms $S$ and a term $t$, whether $S \vdash_{\mathcal I} t$.

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 3.1 (Definition 3.1, terms and subterms), Section 3.2 (Definition 3.3, Figure 3.1 and Definition 3.4) and Section 3.3 (Definition 3.5).
