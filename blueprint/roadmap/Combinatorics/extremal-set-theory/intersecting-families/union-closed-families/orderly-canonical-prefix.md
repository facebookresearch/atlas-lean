# Orderly generation of union-closed families

Let $n$, $k$ and $m$ be natural numbers with
$1 \le m \le k$, and let $A_1, \dots, A_k$ be nonempty subsets of $\Omega_n = \{0, \dots, n-1\}$
with $A_i < A_j$ in the set order whenever $i < j$. Suppose the family
$U = \{\emptyset, A_1, \dots, A_k\}$ is union-closed, every element of $\Omega_n$ lies in some
member of $U$, $U \ne \{\Omega_n, \emptyset\}$, and $U$ is canonical. Then the prefix family
$\{\emptyset, A_1, \dots, A_m\}$ is canonical.

The hypotheses that $U$ is union-closed, covers $\Omega_n$ and differs from
$\{\Omega_n, \emptyset\}$ are not used in the proof. The string of $U$ lists the sort keys of
$A_1, \dots, A_k$ in order, so the string of the prefix family is a prefix of it, and a
permutation that made the prefix family's string smaller would make the string of $U$ smaller.

## Sources

- Gunnar Brinkmann and Robin Deklerck, "Generation of Union-Closed Sets and Moore Families", Journal of Integer Sequences 21 (2018), Article 18.1.7, Theorem `thm:orderly`, source lines 275–281, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Brinkmann/brink6.tex>.
