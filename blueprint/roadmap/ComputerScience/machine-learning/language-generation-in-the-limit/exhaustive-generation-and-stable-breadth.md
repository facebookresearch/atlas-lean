# Exhaustive generation and stable generators with breadth

Let $\mathcal{C} = \{L_1, L_2, \dots\}$ be a countable collection of infinite languages over a countable set $U$, with target $K \in \mathcal{C}$ enumerated by an adversary and $S_t$ the set of strings seen up to step $t$.

(i) **Exhaustive generation.** At each step $t$ a generating algorithm outputs a generator $G_t$ that, if the input stopped at step $t$, would go on to output a sequence $Z_{\ge t}$ of strings; let $Z_{<t}$ be the strings output before step $t$. The algorithm exhaustively generates from $\mathcal{C}$ if for every $K \in \mathcal{C}$ and every enumeration of $K$ there is $t^*$ such that for all $t \ge t^*$ both $|Z_{\ge t} \setminus K| < \infty$ and $S_t \cup Z_{<t} \cup Z_{\ge t} \supseteq K$. There is a countable collection of regular languages that is generatable in the limit but cannot be exhaustively generated, so a trade-off between validity and breadth is inherent in generation in the limit. A countable collection can be exhaustively generated if and only if it satisfies the weak Angluin condition with existence: every $L \in \mathcal{C}$ has a finite $T \subseteq L$ such that every $L' \in \mathcal{C}$ with $T \subseteq L' \subsetneq L$ satisfies $|L \setminus L'| < \infty$. Explicit exhaustive generators for such collections use a membership oracle together with either subset (inclusion) and finite-difference oracles, the latter deciding whether $|L_j \setminus L_i| < \infty$ when $L_i \subsetneq L_j$, or a tell-tale oracle enumerating the sets $T$ (Kalavasis, Mehrotra and Velegkas, Lemmas 7.5 and 7.7).

(ii) **Stable generators.** A generating algorithm is stable if, for every target and every enumeration, its generator eventually stops changing. Since $K \setminus S_t$ shrinks whenever a new string of $K$ appears, a stable generator cannot keep support $K \setminus S_t$; for stable generation its support may therefore repeat seen strings, and the unseen ones are obtained by filtering out $S_t$ separately. A generator has exact breadth for $K$ if its support is $K$, and approximate breadth if its support is contained in $K$ and misses only finitely many strings of $K$; allowing repeats changes no characterization of breadth. For a countable collection, the following are equivalent: $\mathcal{C}$ satisfies Angluin's tell-tale condition (equivalently, is identifiable in the limit); some stable algorithm generates with exact breadth in the limit; some stable algorithm generates with approximate breadth in the limit. No computability or decidability assumption on the generators is needed. Without stability, approximate breadth is achievable exactly for the collections satisfying a weak Angluin condition, by a generator with a membership oracle and either a subset oracle or a tell-tale oracle (Lemmas 7.1 and 7.3), which is strictly weaker than Angluin's condition, so stability separates the two. More generally, any property of a generator that no generator can have for two different languages of $\mathcal{C}$, for instance a strictly lower hallucination rate or perplexity on the target than on every other language, is achievable in the limit only when $\mathcal{C}$ satisfies Angluin's condition.

## Proof sketch

For (i), take $L_\infty = \mathbb{Z}$ and $L_i = \{-i, -i+1, -i+2, \dots\}$ for $i \in \mathbb{Z}$, all regular in binary notation. An adversary enumerates $L_0$ until the generate-only output has only finitely many strings outside $L_0$, then inserts $-1$ and continues as an enumeration of $L_1$ until the same holds for $L_1$, and so on. The resulting sequence enumerates $\mathbb{Z}$, but at infinitely many steps the generate-only output misses infinitely many negative integers, so the algorithm never exhaustively generates $\mathbb{Z}$. The characterization shows that a language violating the weak condition with existence admits such a diagonalization, and conversely builds an exhaustive generator from the finite sets $T$.

For (ii), sufficiency identifies the target and from then on outputs the identified language, whose support is $K$; filtering out $S_t$ gives its unseen strings. Necessity is a diagonalization over a language $L_\infty$ violating Angluin's condition, indexing the languages $L_T \subsetneq L_\infty$ by finite sets $T \subseteq L_\infty$. Since stability cannot be verified at any finite step, the adversary waits until the generator has exhausted its possibilities in each phase, and shows that the generator must either change its support infinitely often or lack approximate breadth infinitely often.

## Depends on

- [Generation in the limit](generation-in-the-limit.md)
- [Identification in the limit from positive examples](identification-in-the-limit.md)
- [Angluin's tell-tale characterization of identifiability in the limit](angluin-tell-tale-characterization.md)

## Proof depends on

- [Every countable collection of languages is generatable in the limit](kleinberg-mullainathan-generation-theorem.md)

## Sources

- M. Charikar, C. Pabbaraju, "Exploring Facets of Language Generation in the Limit", COLT (2025), arXiv:2411.15364, Definition 5, Theorems 3 and 4.
- A. Kalavasis, A. Mehrotra, G. Velegkas, "On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability", ALT (2026), arXiv:2412.18530, Definitions 3.1, 3.2 and 3.14, Theorems 3.5, 3.8 and 3.15, Remarks 3.6 and 3.13, Lemmas 7.1, 7.3, 7.5 and 7.7.
