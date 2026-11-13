# Perfect special honest-verifier zero knowledge

**Perfect special honest-verifier zero knowledge** with simulator `sim` (Damgård, *On
Σ-protocols*): the simulator receives the statement and the challenge `e`, and for every
statement–witness pair in the relation and **every** challenge `e`, the honest
commitment–response distribution for `e` equals `sim x e`. This is stronger than `HVZK`, which
only constrains a uniform challenge; `SpecialHVZK.hvzk` derives `HVZK` from it.
