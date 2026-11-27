# Encoding size of a linear program

Consider a linear program in standard equality form, $\min\{c^\top x : A x = b,\ x \ge 0\}$, with an integer $m \times n$ matrix $A$, $m, n \ge 1$, and integer vectors $b \in \mathbb{Z}^m$, $c \in \mathbb{Z}^n$ (rational data reduce to this case by clearing denominators). The *size* of an integer is $\mathrm{size}(k) = 1 + \lceil \log_2(|k| + 1) \rceil$, the size of a vector or matrix is the sum of the sizes of its entries, and the size of the linear program is

$$\mathrm{size}(LP) = \mathrm{size}(A) + \mathrm{size}(b) + \mathrm{size}(c).$$

The more convenient measure

$$L = \mathrm{size}(\det_{\max}) + \mathrm{size}(b_{\max}) + \mathrm{size}(c_{\max}) + m + n$$

uses $\det_{\max} = \max_{A'} |\det A'|$ over the square submatrices $A'$ of $A$, $b_{\max} = \max_i |b_i|$ and $c_{\max} = \max_j |c_j|$.

## Depends on

- [Linear program](../linear-programming/linear-program.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 11.1, Definitions 6 and 7.
