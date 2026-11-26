# Stabbing planes refute Tseitin formulas in quasi-polynomial size

For every connected graph $H$ of maximum degree $\Delta$ on $n$ vertices and every odd charge function, the Tseitin formula of $H$ has stabbing planes refutations of size $n^{O(\log n)} 2^{O(\Delta)}$ and depth $O(\log^2 n + \Delta)$. In contrast, Tseitin formulas on bounded-degree expanders require resolution size $2^{\Omega(n)}$ and polynomial calculus degree $\Omega(n)$ in characteristic other than $2$.

## Proof sketch

Query the sum of the variables on the edges crossing a balanced cut of $H$, splitting on its value; a balanced-separator recursion halves the number of vertices on each branch, and on each side the parity constraint of the charges combined with the fixed cut value is violated on one side. The integer-free slabs dispose of the parity-violating branches, and a recursion of depth $O(\log n)$ with $O(n)$ possible values per level gives quasi-polynomial size.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)
- [Tseitin CNF](../../propositional-logic/tseitin-transformation/tseitin.md)

## Proof depends on

- [The stabbing planes proof system](stabbing-planes-system.md)
- [Tseitin CNF](../../propositional-logic/tseitin-transformation/tseitin.md)

## Sources

- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), arXiv:1710.03219.
