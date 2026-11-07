# Constant term and row sum of a shifted array

Let $R$ be a commutative semiring, let
$(A_{i,k})_{i,k \in \mathbb{N}}$ be an array with entries in $R$, and let $r \in R$ and
$n \in \mathbb{N}$. For $s \in R$ let $A^{(s)}$ be the $s$-shifted array with entries
$A^{(s)}_{i,j} = \sum_{k=j}^{i} \binom{k}{j} A_{i,k} s^{k-j}$ (an empty sum when $j > i$), and let
$p(X) = \sum_{k=0}^{n} A^{(r)}_{n,k} X^k \in R[X]$ be the $n$-th row polynomial of $A^{(r)}$.
Then $p(0) = A^{(r)}_{n,0} = \sum_{k=0}^{n} A_{n,k} r^k$ and
$p(1) = \sum_{k=0}^{n} A^{(r)}_{n,k} = A^{(r+1)}_{n,0}$.

## Sources

- José Agapito, Ângela Mestre, Maria M. Torres, and Pasquale Petrullo, "On One-Parameter Catalan Arrays," Journal of Integer Sequences 18 (2015), Article 15.5.1, Corollary (equations eqColumn0Rr and eqRowsumsRr), lines 240–245, https://cs.uwaterloo.ca/journals/JIS/VOL18/Agapito/agapito2.tex
