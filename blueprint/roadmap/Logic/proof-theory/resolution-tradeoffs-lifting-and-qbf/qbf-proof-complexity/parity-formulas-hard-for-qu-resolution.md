# QBF parity formulas are hard for QU-resolution but easy for expansion

The QBFs $\mathrm{QParity}_N$, whose unique universal winning strategy computes parity, require exponential-size QU-resolution refutations because strategies extracted from such proofs are in $\mathrm{AC}^0$, yet they have polynomial-size universal expansion refutations.

For $N > 1$ let $\mathrm{xor}(o_1, o_2, o)$ be the four clauses $\{\overline{o}_1 \lor \overline{o}_2 \lor \overline{o},\ o_1 \lor o_2 \lor \overline{o},\ \overline{o}_1 \lor o_2 \lor o,\ o_1 \lor \overline{o}_2 \lor o\}$ defining $o = o_1 \oplus o_2$, and let

$$
\mathrm{QParity}_N = \exists x_1 \dots x_N\, \forall z\, \exists t_2 \dots t_N .\ \mathrm{xor}(x_1, x_2, t_2) \cup \bigcup_{i=3}^{N} \mathrm{xor}(t_{i-1}, x_i, t_i) \cup \{z \lor t_N,\ \overline{z} \lor \overline{t}_N\}.
$$

**Theorem.** Every QU-resolution (hence every Q-resolution) refutation of $\mathrm{QParity}_N$ has size exponential in $N$, while $\mathrm{QParity}_N$ has polynomial-size refutations in universal expansion resolution. Consequently Q-resolution and QU-resolution do not simulate universal expansion resolution, IR-calc or IRM-calc, and winning strategies for universal expansion resolution cannot be computed in $\mathrm{AC}^0$, even for formulas of bounded quantifier complexity.

**General technique.** If a QBF proof system has strategy extraction in $\mathrm{AC}^0$, it requires exponential-size proofs, even for formulas of bounded quantifier complexity; if it has strategy extraction in $\mathrm{P/poly}$, it is not polynomially bounded unless $\mathrm{PH} \subseteq \mathrm{P/poly}$.

## Expansion

For $\exists \vec{x}\, \forall z .\, (z \lor \phi_f) \land (\overline{z} \lor \neg \phi_f)$ the only winning strategy for $z$ is $z \leftarrow f(\vec{x})$; in $\mathrm{QParity}_N$ the $t_i$ are prefix parities, so the strategy for $z$ is parity of $x_1, \dots, x_N$. Strategy extraction turns a QU-resolution refutation of size $s$ into a decision list of size $s^{O(1)}$, an $\mathrm{AC}^0$ circuit of size $s^{O(1)}$, so parity's exponential $\mathrm{AC}^0$ lower bound forces $s$ to be exponential. In universal expansion resolution, expanding $z$ in both polarities gives two copies of the prefix-parity clauses, and one derives clauses stating $t_i^{0/z} = t_i^{1/z}$ inductively, contradicting the expanded clauses $t_N^{0/z}$ and $\overline{t}_N^{1/z}$. Variants of the formulas give similar lower bounds for long-distance Q-resolution and $\mathsf{LQU^+\text{-}Res}$.

## Depends on

- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)
- [Expansion-based QBF calculi: universal expansion resolution and IR-calc](expansion-based-qbf-calculi.md)

## Proof depends on

- [Strategy extraction from Q-resolution refutations](strategy-extraction-from-q-resolution.md)
- [Parity is not in AC0](../../../../TheoryOfComputation/circuit-complexity/lower-bounds-for-ac0-circuits/parity-not-in-ac0.md)

## Sources

- O. Beyersdorff, L. Chew, M. Janota, "Proof complexity of resolution-based QBF calculi", *STACS 2015*, LIPIcs 30, 76-89, doi:10.4230/LIPIcs.STACS.2015.76 (Lemma 12, the definition of the parity formulas in Section 4, Theorem 14, Lemma 15, Corollaries 16 and 17, Theorems 22, 23, 25 and 27).
