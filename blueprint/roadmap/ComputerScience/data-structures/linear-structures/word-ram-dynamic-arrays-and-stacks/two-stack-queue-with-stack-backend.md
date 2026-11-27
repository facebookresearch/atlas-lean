# Two-stack queue with explicit stack backend

A FIFO queue implemented by two stacks (enqueue pushes onto the rear stack; dequeue pops from the front stack, first transferring the rear stack into it when the front is empty) realizes the queue specification over any stack backend, and every adaptive client performing $m$ queue operations satisfies, for a per-call weight bound $K$ of the stack primitives,

$$
\mathrm{weight} + 2K \cdot |\mathrm{rear}_{\mathrm{final}}| \le 3 K m + 2 K |\mathrm{rear}_{\mathrm{initial}}| .
$$

Realized on the Word RAM with physical arrays and resident count registers, a single fixed dispatcher program executes each queue operation in amortized $O(1)$ instructions.

## Proof sketch

The transfer reverses the rear stack onto the front stack, which restores FIFO order. With potential $2K$ times the size of the rear stack, each operation costs at most three stack calls amortized: an enqueue pays one push and two units of potential, and a transfer's pops and pushes are paid by the released potential.

## Depends on

- [Refinement of a data-structure specification by an abstraction function](../../data-structure-interfaces-and-refinement/refinement-by-abstraction-function.md)
- [Potential of a two-list queue](../two-list-queue/potential.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd edition, Addison-Wesley, 1997.
