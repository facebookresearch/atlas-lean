# Error-free cores of ε-matches and full sensitivity of q-gram filtering

**ε-matches.** A pairwise local alignment of length $n$ is a sequence of $n$ columns, each a match or an error (substitution, insertion or deletion); its error rate is the number of error columns divided by $n$. For $\varepsilon > 0$ and a minimal length $n_0$, an *ε-match* is a local alignment with error rate at most $\varepsilon$ and length $n \ge n_0$. Score matches $+1$ and errors $p = 1 - 1/\varepsilon$; an *ε-X-drop* is a run of consecutive columns with total score at most $X p$ (that is, a drop worth $X$ errors).

**Seed length.** An ε-match of length $n$ has at most $\lfloor \varepsilon n \rfloor$ errors, hence at least $n - \lfloor\varepsilon n\rfloor$ match columns split into at most $\lfloor\varepsilon n\rfloor + 1$ error-free segments, so it contains an error-free segment of length at least

$$l(n,\varepsilon) = \left\lceil \frac{n - \lfloor \varepsilon n\rfloor}{\lfloor \varepsilon n \rfloor + 1} \right\rceil .$$

The function $n \mapsto l(n,\varepsilon)$ is sawtooth-shaped (not monotone), but its successive minima increase, so over all $n \ge n_0$ its minimum is

$$s_{\min} = \min\big(l(n_0,\varepsilon),\ l(n_1,\varepsilon)\big),$$

where $n_1$ is the smallest length greater than $n_0$ that allows one more error than $n_0$. An *ε-core* is such an error-free seed segment.

**Lemma 1.** Every ε-match contains at least one ε-core.

**Lemma 2.** If the SWIFT q-gram filter is run with $q = s_{\min}$, then the intersection of any SWIFT hit with an ε-match contains at least one ε-core.

**Theorem (full sensitivity).** Let $\mathcal{M}$ be the set of maximal ε-matches between two sequences that contain no ε-X-drop. The algorithm that filters with SWIFT ($q = s_{\min}$), finds all ε-cores in SWIFT hits, extends them with ε-X-drop extension, and cuts the longest ε-matches from the extensions reports exactly the ε-matches in $\mathcal{M}$.

For example, $n_0 = 20$ and $\varepsilon = 0.1$ give $l(20, 0.1) = \lceil 18/3 \rceil = 6$ and $l(30, 0.1) = \lceil 27/4\rceil = 7$, so $q = s_{\min} = 6$.

## Depends on

- [q-gram filtering lemma for approximate matching](../../q-gram-filtering-lemma-for-approximate-matching.md)
- [Smith–Waterman local alignment](../../sequence-alignment/smith-waterman-local-alignment/README.md)

## Expansion

Errors spread evenly over the alignment minimize the longest error-free run, which gives Lemma 1. SWIFT guarantees, for suitable parallelogram parameters $(w, e, \tau)$ derived from $\varepsilon$ and $n_0$, at least one hit overlapping every ε-match, and the overlap contains at least $\tau$ $q$-hits interspersed by at most $e$ errors; hence some run of consecutive $q$-hits spans at least $q$ error-free columns, which is an ε-core once $q = s_{\min}$ (Lemma 2). In the theorem, every ε-match in $\mathcal{M}$ thus has a detected core; because it contains no ε-X-drop, X-drop extension of that core spans the whole ε-match, and cutting the longest ε-match from the extension and removing overlaps returns it exactly. Setting a seed-and-extend aligner's word size to $s_{\min}$ gives the same lossless seeding guarantee.

## Sources

- B. Kehr, D. Weese, K. Reinert, "STELLAR: fast and exact local alignments", BMC Bioinformatics 12 (Suppl. 9) (2011) S15, Methods (definitions of ε-match, ε-X-drop and ε-core; Lemmas 1–2; Theorem; Fig. 4 example), <https://doi.org/10.1186/1471-2105-12-S9-S15>, PMCID PMC3283304.
