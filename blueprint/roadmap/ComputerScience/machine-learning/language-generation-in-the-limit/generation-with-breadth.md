# Generation with breadth and the membership oracle problem

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. A generating algorithm outputs at each step a generator $G_t$, a randomized procedure whose outputs form a support $\mathrm{supp}(G_t) \subseteq U$. It generates **consistently with breadth in the limit** from $K$ if eventually $\mathrm{supp}(G_t) \cup S_t = K$: it generates only valid strings and every unseen valid string has positive probability ("no hallucination and no mode collapse"). In the statistical setting, samples are drawn i.i.d. from a distribution whose support is $K$ and rates are defined as universal rates in the number of samples. The **membership oracle problem** for a generating algorithm is decidable if, given the description of $G_t$ and a string $x$, one can decide whether $x \in \mathrm{supp}(G_t)$; this holds for every iterative next-token generator whose next-token probabilities are computable exactly as rational numbers (more generally, whenever it is decidable whether a next-token probability is zero).

## Depends on

- [Generation in the limit](generation-in-the-limit.md)
- [Realizable distributions, learning curves and universal rates](../pac-learning/replicable-private-and-universal-learning/universal-multiclass-and-partial-learning/universal-learning-curves-and-littlestone-trees/universal-rate.md)

## Sources

- A. Kalavasis, A. Mehrotra, G. Velegkas, "On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse", STOC (2025), arXiv:2411.09642.
- A. Kalavasis, A. Mehrotra, G. Velegkas, "On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability", ALT (2026), arXiv:2412.18530.
