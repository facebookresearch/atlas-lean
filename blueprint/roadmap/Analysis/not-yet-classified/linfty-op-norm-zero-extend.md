# Zero Extension

For `r ≤ s`, top-left zero extension preserves the matrix seminorm `max_i sum_j ‖Xᵢⱼ‖`, using
the displayed outer-supremum/inner-L1 seminorm structures. This includes `r=0` and requires only
seminormed additive coefficients.

```lean
theorem linfty_opNorm_zeroExtend
    {A : Type u} [SeminormedAddCommGroup A]
    {r s : ℕ} (h : r ≤ s) (X : Matrix (Fin r) (Fin r) A) :
    letI : SeminormedAddCommGroup (Matrix (Fin r) (Fin r) A) :=
      Matrix.linftyOpSeminormedAddCommGroup
    letI : SeminormedAddCommGroup (Matrix (Fin s) (Fin s) A) :=
      Matrix.linftyOpSeminormedAddCommGroup
    ‖Matrix.zeroExtend h X‖ = ‖X‖
```
