# Thirty-two-approximately stable committees always exist

For every instance of committee selection with monotone preferences over committees and every budget $K$, a $32$-approximately stable committee exists. For approval-additive utilities, a constant-approximately stable committee can be computed in polynomial time.

## Proof sketch

First consider a fractional relaxation: Lindahl-type equilibria give a fractional committee that is stable in a fractional sense (shown via a fixed-point argument). Then round it with a dependent-rounding scheme that is robust to every possible deviating coalition simultaneously; analysing the rounding requires a strong concentration bound together with a careful grouping of candidates by weight scale, and the losses combine to the constant $32$.

## Depends on

- [Approximately stable committee](approximately-stable-committee.md)

## Sources

- Z. Jiang, K. Munagala, K. Wang, "Approximately Stable Committee Selection", STOC 2020, arXiv:1910.14008.
