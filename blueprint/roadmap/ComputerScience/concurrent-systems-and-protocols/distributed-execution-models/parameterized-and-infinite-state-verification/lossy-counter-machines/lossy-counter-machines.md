# Lossy counter machines

A lossy counter machine is a Minsky counter machine whose counters may decrease at any moment without the machine noticing. Its configurations are well-quasi-ordered and its steps are monotone, so it is a well-structured transition system: some problems that are undecidable for Minsky machines become decidable, others stay undecidable.

**Counter machines.** A (Minsky) counter machine is $M = (\mathit{Loc}, C, \Delta)$ with a finite set of locations $\mathit{Loc}$, a finite set of counters $C = \{c_1, \dots, c_n\}$ and a finite set of rules $\Delta \subseteq \mathit{Loc} \times \mathit{OP}(C) \times \mathit{Loc}$, where the operations are increments $c_k{+}{+}$, decrements $c_k{-}{-}$ and zero tests $c_k{=}0?$. A configuration is $\langle \ell, a_1, \dots, a_n \rangle \in \mathit{Conf} = \mathit{Loc} \times \mathbb{N}^n$. A *reliable step* $\sigma \to_{\mathrm{std}} \sigma'$ along a rule $(\ell, \mathit{op}, \ell')$ moves from location $\ell$ to $\ell'$ and changes the counters as $\mathit{op}$ says: $c_k{+}{+}$ adds $1$ to $a_k$, $c_k{-}{-}$ subtracts $1$ and requires $a_k > 0$, and $c_k{=}0?$ requires $a_k = 0$ and changes nothing.

**Lossy semantics.** Configurations are ordered by $\langle \ell, a_1, \dots, a_n \rangle \le \langle \ell', a'_1, \dots, a'_n \rangle$ iff $\ell = \ell'$ and $a_i \le a'_i$ for all $i$. A *lossy step* is

$$
\sigma \to_{\mathrm{lossy}} \sigma' \iff \exists \theta, \theta' :\ \sigma \ge \theta,\ \theta \to_{\mathrm{std}} \theta',\ \theta' \ge \sigma',
$$

that is, a reliable step possibly preceded and followed by losses. A *lossy counter machine* (LCM) is a counter machine under this semantics, and runs are sequences of lossy steps. Every reliable step is a lossy step. Lossy steps are monotone: if $\sigma \to_{\mathrm{lossy}} \tau$, then $\sigma' \to_{\mathrm{lossy}} \tau'$ for all $\sigma' \ge \sigma$ and $\tau' \le \tau$; by Dickson's lemma, $(\mathit{Conf}, \le)$ is a well-quasi-ordering.

## Depends on

- [Counter-machine instructions](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/counter-instr.md)
- [One step of a counter machine](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/counter-step.md)

## Proof depends on

None.

## Expansion

The model is due to Mayr. In it, termination, looping and strong inevitability from a given configuration are decidable, as is reachability; uniform termination, repeated inevitability, Büchi acceptance and finiteness of the reachability set are undecidable, with exact positions in the arithmetical hierarchy given by Schnoebelen.

## Sources

- Philippe Schnoebelen, "Lossy Counter Machines Decidability Cheat Sheet", Reachability Problems (RP 2010), Lecture Notes in Computer Science, pp. 51–75, 2010, <https://doi.org/10.1007/978-3-642-15349-5_4>; Sections 2.1–2.3 (operational semantics, lossy steps, monotonicity and Dickson's lemma) and Theorems 3.3, 4.2 and 4.4, read in the open-access copy at <http://www.lsv.fr/Publis/PAPERS/PDF/phs-rp10.pdf>.
