# Decision problems for finitely generated matrix semigroups

For finitely many square matrices of the same size, the membership, vector reachability, scalar reachability and zero-in-the-corner problems ask whether some nonempty product of the given matrices equals a target matrix, maps a vector to a vector, gives a prescribed scalar, or has upper left entry zero.

Let $M_1, \dots, M_k$ be $n \times n$ matrices with entries in a semiring, usually the integers. The semigroup they generate is

$$
\langle M_1, \dots, M_k \rangle = \{ M_{i_1} M_{i_2} \cdots M_{i_m} : m \geq 1,\ 1 \leq i_1, \dots, i_m \leq k \},
$$

the set of all nonempty products of the generators. The following decision problems take the generators as part of the input, together with the data listed.

- *Membership* (matrix reachability): given also a matrix $X$, is $X \in \langle M_1, \dots, M_k \rangle$? The *mortality problem* is the case where $X$ is the zero matrix.
- *Vector reachability*: given also row vectors $u, v$ of length $n$, is there $X \in \langle M_1, \dots, M_k \rangle$ with $uX = v$? The case $v = 0$ is *vector mortality*.
- *Scalar reachability*: given also row vectors $u, v$ of length $n$ and a scalar $a$, is there $N \in \langle M_1, \dots, M_k \rangle$ with $v N u^{\mathsf{T}} = a$?
- *Zero in the upper left corner*: is there $N \in \langle M_1, \dots, M_k \rangle$ with $N_{11} = 0$?
- *Semigroup intersection*: given two finite sets of matrices, do the semigroups they generate have a common element?

A bound such as "for seven $3 \times 3$ matrices" fixes $k$ and $n$ and leaves only the entries of the generators (and of the other data) as input.

## Depends on

None.

## Proof depends on

None.

## Expansion

Membership is sometimes called matrix reachability; mortality, vector reachability and the zero-in-the-corner problem are special cases or close relatives, and over the integers the scalar reachability problem is essentially the corner reachability problem $(M_{i_1} \cdots M_{i_m})_{1n} = a$. Undecidability results for these problems are usually proved by encoding pairs of words as matrices and reducing the Post correspondence problem.

## Sources

- V. Halava, T. Harju and M. Hirvensalo, "Undecidability bounds for integer matrices using Claus instances", *International Journal of Foundations of Computer Science* 18(5):931–948, 2007, doi:10.1142/S0129054107005066; read in the authors' open-access copy at <https://users.utu.fi/harju/articles/HHH_ClausInst.pdf>: Section 1, Problems 3–6 (author copy numbering).
- R. Dong, "Recent advances in algorithmic problems for semigroups", *ACM SIGLOG News* 10(4):3–23, 2023, doi:10.1145/3636362.3636365; read as arXiv:2309.10943v1, whose numbering is used here: Section 1 (semigroup intersection).
