# Empty is Admissible For empty

The empty positive-scale filling is admissible for the empty index-one set inside any ambient
set.

```lean
theorem empty_isAdmissibleFor_empty (t : ℝ) (ht : 0 < t) (G : Set ℂ) :
    (empty t ht).IsAdmissibleFor ∅ G
```
