# Identification in the limit from positive examples

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. An **identifier** maps each finite sequence $w_1, \dots, w_t$ to an index $i_t$. The collection $\mathcal{C}$ is **identifiable in the limit** (from positive data, in the sense of Gold) if there is an identifier such that for every $K \in \mathcal{C}$ and every enumeration of $K$ there exists $t^*$ with $L_{i_t} = K$ for all $t \ge t^*$. Equivalently, viewing languages as binary hypotheses $h_i = \mathbf{1}_{L_i}$, the identifier must eventually output a hypothesis with exactly the target's support.

## Depends on

- [Recognizable languages are exactly the enumerable ones](../../../TheoryOfComputation/computability/enumerators/tm2-recognizable-iff-exists-enumerator.md)

## Sources

- E. M. Gold, "Language Identification in the Limit", Information and Control 10 (1967).
- D. Angluin, "Inductive Inference of Formal Languages from Positive Data", Information and Control 45 (1980).
- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714.
