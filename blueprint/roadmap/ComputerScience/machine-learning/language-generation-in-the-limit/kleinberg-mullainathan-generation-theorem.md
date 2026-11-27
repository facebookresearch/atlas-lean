# Every countable collection of languages is generatable in the limit

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. There is a generator that generates in the limit from every countable collection $\mathcal{C}$ of infinite languages, and it can be implemented with access only to membership queries of the form "is $w \in L_i$?". This contrasts with identification in the limit, which fails for every collection in which some language has no finite tell-tale, for instance any collection containing an infinite language $L$ together with an infinite strictly increasing chain of infinite languages whose union is $L$. Generating from a language is therefore fundamentally easier than identifying it.

## Proof sketch

At step $t$, compute the critical languages among $L_1, \dots, L_t$ and output an unseen string of the critical language with the largest index (searching $U$ in a fixed order and using membership queries). By the nesting lemma that language is contained in every other critical language, in particular, once the target $L_z$ is critical forever and $t \ge z$, the chosen language is a subset of $K$. Hence every output at a step $t \ge \max(z, t^+)$ lies in $K \setminus S_t$. Implementing criticality with membership queries only requires testing inclusions on a growing finite prefix of $U$, which is done by a refined version that checks inclusions up to a slowly growing horizon.

## Depends on

- [Generation in the limit](generation-in-the-limit.md)
- [Identification in the limit from positive examples](identification-in-the-limit.md)

## Proof depends on

- [The target becomes critical forever and critical languages are nested](critical-languages-nested-and-target-eventually-critical.md)
- [Critical languages at a step](critical-language.md)

## Sources

- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757, results (2.1), (4.1)–(4.6) and Section 5.
