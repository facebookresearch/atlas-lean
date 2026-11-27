# Quantified public announcement logics with common knowledge

The logics APALC, GALC and CALC extend arbitrary, group and coalition announcement logic by a common knowledge modality for each group of agents, with announcements quantified over formulas of public announcement logic with common knowledge.

**Languages.** Let $A$ be a finite set of agents and $P$ a countable set of propositional variables. The languages are

$$
\varphi ::= p \mid \neg\varphi \mid (\varphi \wedge \varphi) \mid \Box_a\varphi \mid [\varphi]\varphi \mid \Box_G\varphi \mid Q\varphi, \qquad Q \in \{[!], [G], [\langle G\rangle]\},
$$

with $p \in P$, $a \in A$ and $G \subseteq A$: APALC uses $[!]$, GALC uses $[G]$ and CALC uses $[\langle G\rangle]$. The fragment of APALC without $[!]$ is *public announcement logic with common knowledge* PALC.

**Semantics.** A model $M = (S, \sim, V)$ has a nonempty set $S$ of states, an equivalence relation $\sim_a$ on $S$ for each agent $a$, and a valuation $V$; $\sim_G$ is the reflexive transitive closure of $\bigcup_{a \in G} \sim_a$. Truth is defined by $M_s \models \Box_a\varphi$ iff $\varphi$ is true at every $t$ with $s \sim_a t$; $M_s \models \Box_G\varphi$ iff $\varphi$ is true at every $t$ with $s \sim_G t$; $M_s \models [\psi]\varphi$ iff $M_s \not\models \psi$ or $M^\psi_s \models \varphi$, where $M^\psi$ is the restriction of $M$ to the states satisfying $\psi$; $M_s \models [!]\varphi$ iff $M_s \models [\psi]\varphi$ for every $\psi$ in PALC; $M_s \models [G]\varphi$ iff $M_s \models [\psi_G]\varphi$ for every announcement $\psi_G = \bigwedge_{i \in G}\Box_i\psi_i$ with $\psi_i$ in PALC; and $M_s \models [\langle G\rangle]\varphi$ iff for every such $\psi_G$ there is an announcement $\chi_{A \setminus G}$ of the other agents with $M_s \models \psi_G \to \langle\psi_G \wedge \chi_{A \setminus G}\rangle\varphi$. A formula is *satisfiable* if it is true at some state of some model.

## Depends on

- [Arbitrary, group and coalition announcement logics](../quantified-public-announcement-logics.md)
- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

None.

## Expansion

Without the common knowledge modalities these are the logics APAL, GAL and CAL. Because PALC is strictly more expressive than epistemic logic with common knowledge, it matters that the quantifiers range over PALC formulas; for APAL, GAL and CAL the quantifiers range over the announcement-free fragment, which is as expressive as public announcement logic.

## Sources

- R. Galimullin and L. B. Kuijer, "Satisfiability of arbitrary public announcement logic with common knowledge is Σ¹₁-hard", in *Proceedings of the Conference on Theoretical Aspects of Rationality and Knowledge (TARK 2023)*, Electronic Proceedings in Theoretical Computer Science 379, 2023, pp. 260–271, <https://doi.org/10.4204/EPTCS.379.21>; read as arXiv:2307.05060v1, <https://arxiv.org/abs/2307.05060v1>: Section 2 (Definitions 2.1, 2.2 and 2.3 and Remark 1).
