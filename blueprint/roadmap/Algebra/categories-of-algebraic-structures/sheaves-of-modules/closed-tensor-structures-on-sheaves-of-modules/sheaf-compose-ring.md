# Underlying ring sheaf of a commutative ring sheaf

Let `(C,J)` be a site at universe `u` and `R : Sheaf J CommRingCat.{u}`. Assuming
`J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})`, `sheafComposeRing R` is
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`, the sheaf obtained by forgetting
commutativity of the section rings.
