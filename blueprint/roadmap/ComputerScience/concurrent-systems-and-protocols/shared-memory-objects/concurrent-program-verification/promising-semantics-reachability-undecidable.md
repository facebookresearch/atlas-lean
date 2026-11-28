# Reachability under the promising semantics PS 2.0 is undecidable

For finite-state concurrent programs running under the promising semantics PS 2.0 of C/C++ concurrency, it is undecidable whether given instruction labels of all processes can be reached together, already when every memory access is relaxed. Bounding the number of outstanding promises makes the relaxed fragment decidable.

**Setting (Abdulla, Atig, Godbole, Krishna and Vafeiadis).** A program has finitely many shared memory locations, finitely many processes, and for each process finitely many registers and a finite sequence of labeled instructions: reads $r = x^o$, writes $x^o = r$, read-modify-write operations, fences, assignments of expressions to registers, conditional jumps and assumptions, with access modes $o \in \{\mathsf{rlx}, \mathsf{ra}\}$ (relaxed, release/acquire). Over a *finite data domain*, registers and locations take values in a fixed finite set. PS 2.0 executes such programs on a timestamped message memory: each process keeps views of the memory, may read any message not older than its view, and may *promise* to write a message in the future and *reserve* timestamp intervals. A machine state is *consistent* if every process can fulfill all its outstanding promises running alone from the capped memory. A run is a sequence $MS_0 \to^\ast_{p_{i_1}} MS_1 \to^\ast_{p_{i_2}} \cdots \to^\ast_{p_{i_n}} MS_n$ of blocks of steps, each block by one process, starting from the initial machine state $MS_0$, in which the machine states $MS_1, \dots, MS_n$ after each block are consistent (Section 2.3); the states inside a block need not be. The *reachability problem* asks, given a map $J$ from processes to instruction labels, whether some machine state in which every process $p$ is at label $J(p)$ is reachable by a run. The relaxed fragment uses only $\mathsf{rlx}$ accesses.

**Theorem (Abdulla, Atig, Godbole, Krishna and Vafeiadis).** The reachability problem for concurrent programs over a finite data domain is undecidable under PS 2.0. It remains undecidable for the fragment with only relaxed memory accesses.

The proof also works when executions are restricted to $3$ context switches. Reachability with only release/acquire accesses was already known to be undecidable even without promises (Abdulla, Arora, Atig and Krishna, PLDI 2019). For the relaxed fragment with a bounded number of promises, reachability is decidable, though non-primitive recursive.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The reduction is from the Post correspondence problem. The program has two processes, six memory locations and two registers, whose finite data domain consists of the PCP alphabet, the indices $0, 1, \dots, n$ and two separator symbols. Process $p_1$ can run in a generation mode, in which it promises the indices of a guessed solution to the location $\mathit{index}$ and the letters of the corresponding words $u_i$ to $x$, or in a validation mode, in which it reads indices from $\mathit{index}'$ and checks that it can read the letters of $v_i$ from $y$ for each index $i$, writing back what it read to $\mathit{index}$ and $x$; process $p_2$ only copies $x$ into $y$ and $\mathit{index}$ into $\mathit{index}'$ (Figure 5). The promises are fulfilled exactly when $v_{i_1} \cdots v_{i_k} = u_{i_1} \cdots u_{i_k}$. Under relaxed accesses a reader could skip writes, so the construction uses unboundedly many promises to force each reader to observe every write of the writer in order, which makes the check faithful. The target labels are reachable exactly when the instance has a solution.

A good expansion links pages for the program of Figure 5 and for the lemma that unboundedly many promises force each reader to observe every write of the writer, in order, under relaxed accesses.

## Sources

- Parosh Aziz Abdulla, Mohamed Faouzi Atig, Adwait Godbole, Shankara Narayanan Krishna and Viktor Vafeiadis, "The Decidability of Verification under PS 2.0", Programming Languages and Systems (ESOP 2021), Lecture Notes in Computer Science 12648, pp. 1–29, 2021, <https://doi.org/10.1007/978-3-030-72019-3_1>; read in arXiv:2007.09944v5, <https://arxiv.org/abs/2007.09944v5>: Section 2 (program syntax, PS 2.0, consistency and the reachability problem) and Theorem 3.1 in Section 3 ("Undecidability of Consistent Reachability in PS 2.0"), in the numbering of that version.
