# Stage Product Equivalence

Let `C` and `D` each have a zero object and a Waldhausen structure
without gluing. For `n : ℕ`, use `prodWaldhausen` on `C × D`: cofibrations
and weak equivalences are defined componentwise. There is a categorical
equivalence `Stage (C × D) n ≌ Stage C n × Stage D n`. Its forward functor
is `stageProject C D n`, obtained by projecting a stage diagram and its
morphisms to the two factors. Its inverse is `stagePair C D n`, obtained
by pairing the two diagrams and morphisms componentwise.
