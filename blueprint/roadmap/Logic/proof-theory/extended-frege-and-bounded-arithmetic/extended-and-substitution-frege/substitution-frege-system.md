# Substitution Frege proof systems

A substitution Frege system is a Frege system augmented with the substitution rule: any formula already derived may be instantiated by substituting arbitrary formulas for its propositional variables, so every derived line can be used as if it were an axiom scheme.

Fix a [Frege system](frege-system.md) $F$. A *substitution Frege* ($sF$, also written $SF$) *proof* of $\alpha_k$ is a sequence $\alpha_1,\dots,\alpha_k$ in which every line is an instance of an axiom scheme of $F$, follows from earlier lines by a rule of $F$, or is obtained by the *substitution rule*

$$
\frac{A}{A\sigma}
$$

from an earlier line $A = \alpha_j$, where $\sigma$ simultaneously replaces propositional variables of $A$ by arbitrary formulas. Proof size is the number of symbols.

Facts recorded in the sources:

- The substitution rule is not sound in the sense that its premise implies its conclusion, but it maps tautologies to tautologies, so substitution Frege is a sound and complete propositional proof system.
- Frege, extended Frege and substitution Frege systems are efficiently closed under modus ponens and under substitutions: there are polynomial-time procedures that combine proofs of $\varphi_1,\dots,\varphi_k$ and of $\varphi_1\to\cdots\to\varphi_{k+1}$ into a proof of $\varphi_{k+1}$, and that turn a proof of $\varphi$ into a proof of any substitution instance $\sigma(\varphi)$.

## Expansion

In an ordinary Frege system substitution is only applied to axiom schemes; allowing it on derived lines lets a proof reuse a lemma at many different instances without re-deriving it. For Frege systems closure under substitutions is immediate (apply $\sigma$ to every line, at a cost of a factor $|\sigma(\varphi_k)|$ in size), for substitution Frege it is a rule, and for extended Frege it follows from the p-equivalence of extended Frege with substitution Frege.

## Depends on

- [Frege proof systems](frege-system.md)
- [Extended Frege proof systems](extended-frege-system.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Paola Bruscoli and Alessio Guglielmi, "On the proof complexity of deep inference", *ACM Transactions on Computational Logic* 10(2):14, 2009, doi:10.1145/1462179.1462186, arXiv:0709.1201v3 (Definition 5.7: substitution Frege $sFrege$ with the rule $A/A\sigma$; Definition 4.1 for Frege systems).
- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 3: the substitution rule and the systems $EF$ and $SF$; Definitions 4.1 to 4.3 and Proposition 4.4: efficient closure of $F$, $EF$, $SF$ under modus ponens and substitutions; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001; ECCC report TR98-067, <https://eccc.weizmann.ac.il/report/1998/067/> (Section 2.1: in $sF$ each line of a Frege proof may be used as if it were an axiom).
