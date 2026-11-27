# Big-step semantics with read counts for the imperative language with arrays

The counted big-step relation $c : s \Downarrow^n t$ says that the statement $c$ takes the state $s$ to the state $t$ performing $n$ array reads. It is the least relation satisfying the following rules, where $|a|$ is the length of $a$:

- $\mathtt{skip} : s \Downarrow^0 s$ and $(x := e) : s \Downarrow^0 s[x \mapsto e(s)]$;
- $(x := a[e]) : s \Downarrow^1 s[x \mapsto a_{e(s)}]$ whenever $e(s) < |a|$;
- if $c_1 : s \Downarrow^n u$ and $c_2 : u \Downarrow^m t$, then $(c_1 ; c_2) : s \Downarrow^{n+m} t$;
- if $b$ is true in $s$ and $c_1 : s \Downarrow^n t$, then $(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2) : s \Downarrow^n t$; if $b$ is false in $s$ and $c_2 : s \Downarrow^n t$, the same holds;
- if $b$ is false in $s$, then $(\mathtt{while}\ b\ \mathtt{do}\ c) : s \Downarrow^0 s$; if $b$ is true in $s$, $c : s \Downarrow^n u$ and $(\mathtt{while}\ b\ \mathtt{do}\ c) : u \Downarrow^m t$, then $(\mathtt{while}\ b\ \mathtt{do}\ c) : s \Downarrow^{n+m} t$.

These are the rules of the big-step semantics with a count attached, each read contributing one; loop invariants play no role.
