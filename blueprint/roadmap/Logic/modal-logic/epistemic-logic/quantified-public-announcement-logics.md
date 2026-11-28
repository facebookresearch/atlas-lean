# Arbitrary, group and coalition announcement logics

APAL, GAL and CAL extend multi-agent epistemic logic with operators that quantify over public announcements: $\Box\varphi$ (after every announcement), $[G]\varphi$ (after every joint announcement of what the agents in $G$ know) and $[\langle G\rangle]\varphi$ (whatever $G$ announces, the other agents can respond so that $\varphi$ is true).

**Language.** Fix a finite set $A$ of agents and a countable set $P$ of atoms. Epistemic logic EL has formulas $\varphi ::= p \mid \neg\varphi \mid (\varphi \wedge \varphi) \mid K_a\varphi$ with $p \in P$, $a \in A$. For $G \subseteq A$, $\mathrm{EL}^G$ is the set of formulas $\bigwedge_{a \in G} K_a \varphi_a$ with each $\varphi_a \in \mathrm{EL}$. The logics add to EL, respectively,

- APAL: public announcements $[\psi]\varphi$ and arbitrary announcements $\Box\varphi$;
- GAL: public announcements and group announcements $[G]\varphi$ for $G \subseteq A$;
- CAL: public announcements and coalition announcements $[\langle G\rangle]\varphi$ for $G \subseteq A$,

where $\psi$ and $\varphi$ range over the extended language.

**Semantics.** A model is $M = (S, \sim, V)$ with $S$ a nonempty set of worlds, an equivalence relation $\sim_a$ on $S$ for each agent $a$ and a valuation $V : P \to \wp(S)$. Atoms, Booleans and $K_a$ (truth in all $\sim_a$-related worlds) are as usual, and

$$
\begin{aligned}
M_s \models [\psi]\varphi &\iff M_s \models \psi \text{ entails } M^\psi_s \models \varphi,\\
M_s \models \Box\varphi &\iff M_s \models [\psi]\varphi \text{ for every } \psi \in \mathrm{EL},\\
M_s \models [G]\varphi &\iff M_s \models [\psi]\varphi \text{ for every } \psi \in \mathrm{EL}^G,\\
M_s \models [\langle G\rangle]\varphi &\iff \text{for every } \psi \in \mathrm{EL}^G \text{ there is } \psi' \in \mathrm{EL}^{A \setminus G} \text{ with } M_s \models \psi \to \langle\psi \wedge \psi'\rangle\varphi,
\end{aligned}
$$

where $M^\psi$ is the restriction of $M$ to the worlds satisfying $\psi$ and $\langle\chi\rangle\varphi$ abbreviates $\neg[\chi]\neg\varphi$, that is, $\chi \wedge [\chi]\varphi$. The coalition clause is that of Galimullin and Kuijer (Definition 2.3); the source read prints it with $[\psi \wedge \psi']\varphi$, which agrees with it for $G = A$, the only case its proof uses, but for $G \ne A$ would make $[\langle G\rangle]\varphi$ valid, since some $\psi' \in \mathrm{EL}^{A \setminus G}$ is false everywhere. The announcements quantified over are epistemic formulas, without announcement operators. A formula is *satisfiable* if it is true at some world of some model.

## Depends on

- [Epistemic models](model.md)
- [Epistemic formulas](formula.md)

## Proof depends on

None.

## Expansion

Public announcement logic, with $[\psi]$ alone, is no more expressive than EL and so decidable. The quantifiers make the logics more expressive: in APAL, $\Box\varphi$ ranges over all epistemic formulas, which lets a formula force structure up to $n$-bisimilarity for every $n$; in GAL the announcing agents can only remove worlds they can distinguish from the actual one; in CAL there is an alternation between the coalition's announcement and the response of the others, in the style of game logics and ATL.

## Sources

- T. Ågotnes, H. van Ditmarsch and T. French, "The undecidability of quantified announcements", *Studia Logica* 104(4):597–640, 2016, doi:10.1007/s11225-016-9657-0; read as the corrected version arXiv:2405.15671v2, <https://arxiv.org/abs/2405.15671v2>: Section 2 (syntax and semantics of APAL, GAL and CAL).
- R. Galimullin and L. B. Kuijer, "Satisfiability of arbitrary public announcement logic with common knowledge is Σ¹₁-hard", in *Proceedings of the Conference on Theoretical Aspects of Rationality and Knowledge (TARK 2023)*, Electronic Proceedings in Theoretical Computer Science 379, 2023, pp. 260–271, <https://doi.org/10.4204/EPTCS.379.21>; read as arXiv:2307.05060v1, <https://arxiv.org/abs/2307.05060v1>: Definition 2.3 (the coalition clause).
