# Share-level execution of the gates of a BGW program

Let $F$ be a field and $\mathrm{Party}$ a finite type of parties, with Shamir parameters giving a threshold $t$ and an evaluation point $\alpha_i \in F$ for each party $i$, and let $\lambda : \mathrm{Party} \to F$ be arbitrary weights (the definition assumes no recombination property of $\lambda$). Fix a straight-line program over addition and multiplication gates with $\mathrm{inputCount}$ inputs and $\mathrm{gateCount}$ gates, input share functions $\mathrm{inShares}(k) : \mathrm{Party} \to F$, and one tape $\mathrm{tapeMul}(g) : \mathrm{Party} \to F^t$ per gate $g$. The share function $\mathrm{Party} \to F$ of each gate is defined by recursion on the program:

- the empty program has no gates;
- for a program $p$ followed by a newly appended last gate with operation $\mathrm{op}$ and argument wires $w_0, w_1$, the share functions of the earlier gates are those of $p$, computed with $\mathrm{tapeMul}$ restricted to the earlier gates; the share function of the last gate is the [new-gate share function](new-gate-share.md) of $\mathrm{op}$ and $w_0, w_1$, with the tape $\mathrm{tapeMul}(\text{last})$, where an input wire $k$ carries $\mathrm{inShares}(k)$ and an earlier-gate wire carries that gate's share function.

For addition the new share of party $j$ is $s_0(j) + s_1(j)$; for multiplication it is $\sum_i \lambda_i \cdot \mathrm{share}_j\bigl(s_0(i)\,s_1(i);\ \tau_i\bigr)$, party $j$'s Shamir share of party $i$'s local product under party $i$'s tape.
