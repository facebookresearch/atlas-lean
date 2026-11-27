# Rouché–Capelli theorem

Let $K$ be a field, $A$ an $m \times n$ matrix over $K$ with $n$ finite and $b \in K^m$. Then the linear system $Ax = b$ has a solution $x \in K^n$ if and only if the rank of $A$ equals the rank of the augmented matrix $(A \mid b)$.

## Idea

The system $Ax = b$ asks whether $b$ is a linear combination of the columns of $A$. Adjoining $b$ as an extra column leaves the column space, and so the rank, unchanged exactly when $b$ already lies in it; otherwise the rank goes up by one. When a solution exists, the solutions form an affine space of dimension $n - \operatorname{rank} A$, so the solution is unique exactly when the rank equals the number of unknowns. In practice both ranks are read off a row echelon form.

## Statements

- [Rouché–Capelli theorem](rouche-capelli.md)
