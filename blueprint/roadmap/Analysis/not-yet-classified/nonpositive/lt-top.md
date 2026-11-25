# Lt top

Every domain value of a nonpositive subharmonic function is strictly below positive infinity.

```lean
theorem IsNonpositiveSubharmonicOn.lt_top {u : ℂ → EReal} {D : Set ℂ}
    (h : IsNonpositiveSubharmonicOn u D)
    {z : ℂ} (hz : z ∈ D) : u z < ⊤
```
