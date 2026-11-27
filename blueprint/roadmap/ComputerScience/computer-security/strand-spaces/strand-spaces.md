# Strand spaces

Let $A$ be a set of terms, the algebra freely generated from a set $T$ of texts and a set $K$ of keys by encryption $\{h\}_K$ and concatenation $g\,h$. The *subterm*
relation $\sqsubset$ is the smallest relation with $a \sqsubset a$, $a \sqsubset \{g\}_K$ if $a \sqsubset g$, and $a \sqsubset g\,h$ if $a \sqsubset g$ or $a \sqsubset h$; so a key $K$ is
a subterm of $\{g\}_K$ only if it is a subterm of $g$. A *signed term* is $+t$ (transmission) or $-t$ (reception) for $t \in A$. A *strand space* over $A$ is a set
$\Sigma$ with a trace mapping $\mathrm{tr} : \Sigma \to (\pm A)^*$ to finite sequences of signed terms.

A *node* is a pair $\langle s, i\rangle$ with $s \in \Sigma$ and $1 \le i \le \mathrm{length}(\mathrm{tr}(s))$; its term $\mathrm{term}(\langle s, i\rangle)$ is the $i$-th signed term of
$\mathrm{tr}(s)$. There is an edge $n_1 \to n_2$ when $\mathrm{term}(n_1) = +a$ and $\mathrm{term}(n_2) = -a$ for some $a$, and an edge $\langle s, i\rangle \Rightarrow \langle s, i+1\rangle$
between consecutive nodes of a strand; $n' \Rightarrow^+ n$ means that $n'$ precedes $n$ on the same strand. A term $t$ *occurs* in $n$ if $t \sqsubset \mathrm{term}(n)$;
$t$ *originates* on $n$ if $\mathrm{term}(n)$ is positive with $t \sqsubset \mathrm{term}(n)$ and $t \not\sqsubset \mathrm{term}(n')$ whenever $n' \Rightarrow^+ n$; and $t$ is *uniquely
originating* if it originates on exactly one node, as a nonce or session key does.

## Sources

- F. J. Thayer Fábrega, J. C. Herzog and J. D. Guttman, "Strand spaces: proving security protocols correct", *Journal of Computer Security* 7:191–230, 1999, copy at <http://web.cs.wpi.edu/~guttman/pubs/jcs_strand_spaces.pdf>: Section 2.1 (Definitions 2.1–2.3) and Section 2.4 (Axioms 1–2 on free encryption and Definition 2.11, the subterm relation).
