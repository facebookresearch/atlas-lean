# BWT from recursive prefix-free parsing

**Prefix-free parsing (PFP).** Given a text $T$ over an ordered alphabet, a window size $w$ and a modulus $p$, append $w$ copies of a sentinel symbol $\#$ (smaller than every symbol) to both ends of $T$, and let the trigger strings $E$ be the length-$w$ windows $t$ with Karp–Rabin hash $H_p(t)\equiv 0$ together with $\#^w$. Cutting the padded text at trigger strings, so that consecutive phrases overlap in exactly one trigger string, yields a dictionary $D$ of distinct phrases (stored in lexicographic order) and a parse $P$ listing the dictionary ranks of the phrases in text order. The basic property is that **the set $S$ of distinct proper phrase suffixes of length at least $w$ is prefix-free** (no element is a prefix of another).

**Ordering consequences of PFP.** (Corollary 1) If $T[i]$ and $T[j]$ are followed in $T$ by distinct proper phrase suffixes $\alpha\neq\beta$ with $|\alpha|,|\beta|\ge w$, then $T[i]$ precedes $T[j]$ in $\mathrm{BWT}_T$ iff $\alpha\prec\beta$. (Lemma 2) If two suffixes $t,t'$ of $T$ begin with the same proper phrase suffix $\alpha$, and $q,q'$ are the corresponding suffixes of the parse, then $t\prec t'$ implies $q\prec q'$.

**Recursive PFP.** Run PFP on $T$ with parameters $(w_1,p_1)$, obtaining $(D_T,P_T)$; then run PFP on the integer string $P_T$ with $(w_2,p_2)$, obtaining $(D_P,P_P)$. Symbols of $D_P$ ("meta-characters") are ranks of $D_T$ phrases. Let $S_T$, $S_P$ be the proper phrase suffixes of length $\ge w_1$ (resp. $\ge w_2$) of $D_T$ (resp. $D_P$). For $\alpha\in S_T$ let $D_\alpha\subseteq D_T$ be the phrases ending in $\alpha$, and let $S_\beta\subseteq S_P$ be the proper meta-phrase suffixes preceded in $P_T$ by a phrase of $D_\alpha$. Then $\alpha$ is

- **easy** if every phrase of $D_\alpha$ has the same character immediately before $\alpha$;
- **hard-easy** if two phrases of $D_\alpha$ differ in that character, but no two occurrences in $P_T$ of phrases of $D_\alpha$ are followed by the same element of $S_\beta$;
- **hard-hard** otherwise (different preceding characters, and two phrases of $D_\alpha$ precede the same proper meta-phrase suffix).

**Theorem 1.** Given $D_T$, $D_P$ and $P_P$, the BWT of $T$ can be computed in $O(|D_T|+|D_P|+|P_P|)$ workspace, without storing $P_T$.

## Expansion

By the prefix-free property, the BWT is partitioned into consecutive ranges, one per $\alpha\in S_T$ in lexicographic order; the start of the range is the total frequency of smaller phrase suffixes and its length is the frequency of $\alpha$. An easy range is filled with its single preceding character. For hard suffixes, Lemma 2 says the order of occurrences of $\alpha$ is the order of what follows them in the parse, and the second-level parse resolves that order: scan $S_P$ lexicographically through a table indexed by proper meta-phrase suffixes; a meta-suffix preceded by a single occurrence of a phrase in $D_\alpha$ fixes the next occurrence directly (hard-easy), while a meta-suffix shared by several occurrences is resolved by the positions of the containing meta-phrases in $\mathrm{BWT}_{P_P}$, stored as a grid with $O(|P_P|)$ rows and $O(|D_P|)$ columns (hard-hard). Two tables of sizes $O(|S_T|)$ and $O(|S_P|)$ plus the grid give the stated workspace. On repetitive collections $|D_T|+|D_P|+|P_P|$ is far smaller than $|P_T|$, which is the memory bottleneck of single-level PFP.

## Sources

- Ferro E, Oliva M, Gagie T, Boucher C, "Building a pangenome alignment index via recursive prefix-free parsing" (2024), Lemma 1, Corollary 1, Lemma 2, Definitions 1-6 and Theorem 1 (Method details, "Overview of recursive prefix-free parsing"), the latter attributed there to Oliva et al., <https://doi.org/10.1016/j.isci.2024.110933>, PMCID PMC11465122.
