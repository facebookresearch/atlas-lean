# Gate sharing polynomials of a BGW program

Let $F$ be a field and $\mathrm{Party}$ a finite type of parties, with Shamir parameters giving a threshold $t$ and an evaluation point $\alpha_i \in F$ for each party $i$, and let $\lambda : \mathrm{Party} \to F$ be arbitrary weights (the definition assumes no recombination property of $\lambda$). Fix a straight-line program over addition and multiplication gates with $\mathrm{inputCount}$ inputs and $\mathrm{gateCount}$ gates, input sharing polynomials $\mathrm{inPolys}$, and one tape $\mathrm{tapeMul}(g) : \mathrm{Party} \to F^t$ per gate $g$. The gate polynomials are defined by recursion on the program:

- the empty program has no gates;
- for a program $p$ followed by a newly appended last gate with operation $\mathrm{op}$ and argument wires $w_0, w_1$, the polynomials of the earlier gates are those of $p$, computed with $\mathrm{tapeMul}$ restricted to the earlier gates; the polynomial of the last gate is the [new-gate polynomial](new-gate-poly.md) of $\mathrm{op}$ and $w_0, w_1$, with the tape $\mathrm{tapeMul}(\text{last})$, where an input wire $k$ carries $\mathrm{inPolys}(k)$ and an earlier-gate wire carries that gate's polynomial.

Every gate is given its own tape; only multiplication gates use it.
