# Linear recurrence sequences as observations of companion-matrix dynamics

Linear recurrence sequences are a separate definition and are not restated here. This node states the matrix
correspondence.

Let $k \ge 1$. An integer sequence satisfies $u_{n+k} = \sum_{i<k} c_i u_{n+i}$ with integer $c_i$ if and only if
$u_n = e_1^{\mathsf T} M^n s$ for all $n$, where $s = (u_0, \dots, u_{k-1})^{\mathsf T}$ and $M$ is the companion matrix with
$M_{i,i+1} = 1$ for $i < k$, last row $(c_0, \dots, c_{k-1})$ and all other entries $0$; that is, $u$ is the first-coordinate
observation of the autonomous linear system $x_{n+1} = M x_n$, $x_0 = s$. Conversely, for every integer
$k \times k$ matrix $M$ and integer vectors $c$, $x$, the sequence $c^{\mathsf T} M^n x$ satisfies the integer recurrence given by the
characteristic polynomial of $M$, of order at most $k$ (Cayley–Hamilton).

## Sources

- The Skolem Landscape (Invited Talk) — J. Worrell, ICALP 2023, LIPIcs 261, 5:1-5:2, DOI 10.4230/LIPIcs.ICALP.2023.5. <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.5> Abstract (integer linear recurrence sequences).
- Positivity Problems for Low-Order Linear Recurrence Sequences — J. Ouaknine, J. Worrell, SODA 2014, arXiv:1307.2779, Sec. 2 (matrix form $u_n = v^{\mathsf T} M^n w$ with the transposed companion matrix, and the Cayley–Hamilton converse). <https://arxiv.org/abs/1307.2779>
