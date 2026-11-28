# Core floating-point operations in the normal range

The Lean core models of binary32 and binary64 compute addition, multiplication and fused multiply-add by rounding the exact result once, to nearest with ties to even. When that exact result lies in the normal range of the format, the computed value is the rounding $\mathrm{fl}_p$ of the exact result at the format's precision.

- [Binary32 addition rounds the exact sum in the normal range](binary32-addition-rounds-in-the-normal-range.md)
- [Binary32 multiplication rounds the exact product in the normal range](binary32-multiplication-rounds-in-the-normal-range.md)
- [Binary64 fused multiply-add rounds the exact result once in the normal range](binary64-fused-multiply-add-rounds-once-in-the-normal-range.md)

## Related topics

- [Binary64 addition rounds the exact sum in the normal range](../../../not-yet-classified/float-model/to-rat-add.md)
- [Binary64 multiplication rounds the exact product in the normal range](../../../not-yet-classified/float-model/to-rat-mul.md)
- [IEEE operations agree with rounding in the normal range](../ieee-operations-agree-with-rounding-in-the-normal-range.md): the corresponding statement for a total IEEE-style semantics.
