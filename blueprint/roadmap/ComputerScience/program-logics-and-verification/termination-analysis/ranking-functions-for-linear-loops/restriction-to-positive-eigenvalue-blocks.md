# Restriction to positive-eigenvalue blocks

Let $P_3 : \mathbf{while}\ (B_1 y_1 + \dots + B_K y_K > 0)\ \{\, y_1 := J_1 y_1; \dots; y_K := J_K y_K \,\}$ be a homogeneous linear loop whose update is in [real Jordan form](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/real-jordan-form.md), with $J_i$ a Jordan block for a real eigenvalue $\lambda_i$ or a real block $RJ$ for a pair of complex eigenvalues, and with the matrices $B_i$ obtained by partitioning the columns of the guard matrix accordingly. Let $S_+$ be the set of indices $i$ whose block has a real eigenvalue $\lambda_i > 0$. Then $P_3$ terminates on every real input if and only if the loop

$$P_4 : \mathbf{while}\ \Bigl(\sum_{j \in S_+} B_j y_j > 0\Bigr)\ \{\, y_j := J_j y_j \text{ for } j \in S_+ \,\}$$

terminates on every real input.

## Depends on

- [Real Jordan form](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/real-jordan-form.md)

## Expansion

This page becomes ready once these prerequisites are checked:

- A complete proof of the converse direction, whose key step (the dominant term for large $i$) the source claims without proof (source check)

## Sources

- A. Tiwari, "Termination of linear programs", *Computer Aided Verification (CAV 2004)*, LNCS 3114, Springer, 2004, pp. 70–82, author copy <https://www.csl.sri.com/users/tiwari/papers/cav04.pdf>, Section 3, Lemma 1 and its proof sketch.
