# The activity lemma for PCF

In sequential PCF (without parallel constants), the *active subprogram* of a program $M$ is defined by: if $M$ has one of the forms $(\lambda \alpha.\, M_1) \cdots$,
$(Y \cdots)$, $(+1)\, c$, $(-1)\, c$, $Z\, c$ or $\supset\, c \cdots$, with $c$ a constant, then $M$ is its own active subprogram; if $M$ has one of the forms $(\pm 1)\, M_1$, $Z\, M_1$ or
$\supset\, M_1 \cdots$ with $M_1$ not a constant, then the active subprogram of $M$, if any, is that of $M_1$. A program with no active subprogram is a constant.

**Lemma (activity).** Let $C[M_1, \dots, M_m]$ be a program that terminates with value $c$, where $M_1, \dots, M_m$ are closed terms. Then either

- $C[M_1', \dots, M_m']$ terminates with value $c$ for all closed terms $M_1', \dots, M_m'$ of the appropriate types, or
- there are a context $D[\ ,\dots,\ ]$, an index $1 \le i \le m$ and indices $d_1, \dots, d_k$ such that for all closed $M_1', \dots, M_m'$ of the appropriate types,
  $C[M_1', \dots, M_m'] \to^* D[M_{d_1}', \dots, M_{d_k}']$ and the active subprogram of $D[M_{d_1}', \dots, M_{d_k}']$ exists and is either the active subprogram of a term of
  the form $(M_i' \cdots)$, or has one of the forms $((\pm 1)\, M_i')$, $(Z\, M_i')$ or $(\supset\, M_i' \cdots)$.

So the deterministic evaluation of a PCF program either never consults the holes or reaches a point where it must evaluate one particular hole first.
This sequentiality makes parallel functions such as parallel or undefinable in PCF.

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 4, the definition of the active subprogram and Lemma 4.2 (activity lemma), with its use in the argument on page 236.
