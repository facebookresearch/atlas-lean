# Guarded fixed points

Recursive definitions in Iris whose recursive occurrences are guarded by a later have unique solutions, with no restriction on variance: the later modality is contractive, every other connective is non-expansive, and the step-indexed Banach theorem applies.

**Theorem.** Let $M$ be a unital camera and $X = T_1 \xrightarrow{ne} \cdots \xrightarrow{ne} T_k \xrightarrow{ne} \mathrm{UPred}(M)$ for OFEs $T_1, \dots, T_k$, $k \ge 0$. Then

1. the interpretation of $\triangleright$, applied pointwise, is a contractive map $X \to X$, and the interpretations of the other connectives are non-expansive;
2. a non-expansive map composed with a contractive one is contractive, so for a well-typed guarded $\mu x{:}\tau.\, t$ with $[\![\tau]\!] = X$, the map $u \mapsto [\![t]\!]_{\rho[x \leftarrow u]}$ is contractive;
3. every contractive map $X \to X$ has a unique fixed point.

## Depends on

- [Iris base logic](iris-base-logic.md)
- [Uniform predicates](uniform-predicates.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)
- [Banach fixed-point theorem for complete OFEs](../step-indexed-foundations/banach-fixed-point-theorem-for-cofes.md)

## Proof depends on

- [Iris base logic](iris-base-logic.md)
- [Uniform predicates](uniform-predicates.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)
- [Completeness of non-expansive function spaces](../step-indexed-foundations/completeness-of-non-expansive-function-spaces.md)
- [Banach fixed-point theorem for complete OFEs](../step-indexed-foundations/banach-fixed-point-theorem-for-cofes.md)

## Expansion

For 1: if $P \overset{m}{=} Q$ for all $m < n$, then at an index $k \le n$ with $k \in \mathcal{V}(a)$ either $k = 0$, where both later predicates hold, or $k - 1 < n$, where $P$ and $Q$ agree; so $\triangleright P \overset{n}{=} \triangleright Q$. For 2: in a guarded body every occurrence of $x$ lies under $\triangleright$, and the connectives above it are non-expansive, so the composite is contractive (the source's argument). For 3: $X$ is complete because $\mathrm{UPred}(M)$ is and function spaces into a complete OFE are complete, and it is inhabited, so the Banach theorem applies. Weakest preconditions are defined this way.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5.6 (guarded fixed points: contractiveness of later, non-expansiveness of the other connectives, composition) and Section 8.1 (completeness of T1 -> ... -> UPred(M)).
