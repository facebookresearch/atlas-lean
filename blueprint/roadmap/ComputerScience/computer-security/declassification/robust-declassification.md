# Robust declassification

Let the security levels form a product lattice $\mathcal L = \mathcal L_C \times \mathcal L_I$ of confidentiality and integrity, $\ell = (C(\ell), I(\ell))$, and let a lattice point
$A$ describe the attacker: it reads data at or below $(C(A), \top_I)$ and modifies data at or above $(\bot_C, I(A))$. Programs are commands of a while language with
$v := \mathrm{declassify}(e, \ell)$ over variables typed by $\Gamma$; memories are *indistinguishable at* $\ell$, $M_1 =_\ell M_2$, when they agree on the variables of level
at most $\ell$, and traces $t_1, t_2$ of configurations are *high-stutter equivalent up to* $\ell$, $t_1 \sim_\ell t_2$, when their sequences of $\ell$-restricted memories
agree after collapsing the steps that are invisible at $\ell$, where invisibility is a property of the transition label: a step is collapsed
only if it is not an assignment to a variable of level at most $\ell$, so a visible assignment counts even when it rewrites the old value. Configurations are *weakly indistinguishable* up to $\ell$, $\langle M_1, c_1\rangle \approx_\ell \langle M_2, c_2\rangle$, if their
traces are $\sim_\ell$-equivalent whenever both terminate, and *strongly indistinguishable*, $\langle M_1, c_1\rangle \cong_\ell \langle M_2, c_2\rangle$, if moreover both terminate.

A *fair attack* is a declassify-free command built from $\mathbf{skip}$, sequencing, assignments $v := e$, conditionals and loops whose variables all have one level
$\ell$ with $C(\ell) \sqsubseteq C(A)$ and $I(A) \sqsubseteq I(\ell)$. A *high-integrity context* $c[\vec\bullet]$ is a command with holes $\bullet$, and $c[\vec a]$ fills them with
attacks. The context $c[\vec\bullet]$ is *robust* with respect to fair attacks at level $A$ if for all memories $M_1, M_2$ and fair-attack vectors $\vec a, \vec a'$,

$$\langle M_1, c[\vec a]\rangle \cong_{(C(A), \top_I)} \langle M_2, c[\vec a]\rangle \implies \langle M_1, c[\vec a']\rangle \approx_{(C(A), \top_I)} \langle M_2, c[\vec a']\rangle:$$

an active attacker who changes the attack code learns nothing about secrets beyond what a passive attacker observing $c[\vec a]$ learns.

## Depends on

- [Security levels, policies and low equivalence](../information-flow/security-levels-policies-and-low-equivalence.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 3 (the product lattice, the attacker model and the language), Section 4 (Definitions 2–5 on trace projections and indistinguishability, and Definitions 7–9: fair attacks, high-integrity contexts and robustness).
