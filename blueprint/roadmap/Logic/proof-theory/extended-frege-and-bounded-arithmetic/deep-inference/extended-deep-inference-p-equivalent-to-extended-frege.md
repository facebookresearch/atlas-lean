# Extended and substitution deep inference are p-equivalent to extended Frege

Adding Tseitin extension or the substitution rule to the deep-inference system SKSg gives systems that are p-equivalent to extended Frege and substitution Frege, so all four extended formalisms have the same proof complexity.

Let $xFrege$ and $sFrege$ be extended Frege and substitution Frege. An *extended SKSg proof* (system $xSKSg$) of $\alpha$ is an SKSg derivation with conclusion $\alpha$ and premise $[\bar A_1\vee\beta_1]\wedge[\bar\beta_1\vee A_1]\wedge\dots\wedge[\bar A_h\vee\beta_h]\wedge[\bar\beta_h\vee A_h]$, where $A_1,\bar A_1,\dots,A_h,\bar A_h$ are mutually distinct and each $A_i$ occurs neither in $\beta_1,\dots,\beta_i$ nor in $\alpha$. An *sSKSg proof* is an SKSg proof that may also use the substitution rule $A/A\sigma$ at top level (not inside a context).

**Theorem (Bruscoli–Guglielmi).**

1. Every $xFrege$ proof of length $l$ and size $n$ becomes an $xSKSg$ proof of length $O(l)$ and size $O(n^2)$; every $xSKSg$ proof of size $n$ becomes an $xFrege$ proof of length $O(n^4)$ and size $O(n^5)$. Hence $xFrege$ and $xSKSg$ are p-equivalent.
2. Every $xSKSg$ proof of size $n$ becomes an $sSKSg$ proof of length $O(n)$ and size $O(n^2)$, so $sSKSg$ p-simulates $xSKSg$.
3. Every $sSKSg$ proof of size $n$ becomes an $sFrege$ proof of length $O(n^4)$ and size $O(n^5)$, so $sFrege$ p-simulates $sSKSg$.

Combined with the p-equivalence of $xFrege$ and $sFrege$, the systems $xFrege$, $sFrege$, $xSKSg$ and $sSKSg$ are all p-equivalent.

## Expansion

Parts 1 and 3 reuse the Frege/SKSg translations of the non-extended case, applied to the derivation from the extension premises, respectively to the SKSg segments between substitution steps. For part 2, start from $\mathsf t$, introduce $\bar\gamma\vee\gamma$ by identity where $\gamma$ is the conjunction of extension premises, run the $xSKSg$ derivation inside the context $\bar\gamma\vee\{\ \}$, and then remove the extension clauses one at a time, from the last to the first: substitute $\beta_i$ for $A_i$, contract, and cut away $\beta_i\wedge\bar\beta_i$. The freshness conditions ensure that these substitutions do not affect $\alpha$ or the earlier definitions.

## Depends on

- [The deep-inference system SKS in the calculus of structures](calculus-of-structures-system-sks.md)
- [Extended Frege proof systems](../extended-and-substitution-frege/extended-frege-system.md)
- [Substitution Frege proof systems](../extended-and-substitution-frege/substitution-frege-system.md)

## Proof depends on

- [Deep inference and Frege systems are p-equivalent](sks-p-equivalent-to-frege.md)
- [Extended Frege and substitution Frege are p-equivalent](../extended-and-substitution-frege/extended-frege-p-equivalent-to-substitution-frege.md)

## Sources

- Paola Bruscoli and Alessio Guglielmi, "On the proof complexity of deep inference", *ACM Transactions on Computational Logic* 10(2):14, 2009, doi:10.1145/1462179.1462186, arXiv:0709.1201v3 (Section 5: Definitions 5.1, 5.3, 5.7 and 5.9, Remarks 5.2 and 5.10, Theorems 5.4, 5.5, 5.8, 5.11 and 5.13, Corollaries 5.6, 5.12 and 5.14).
