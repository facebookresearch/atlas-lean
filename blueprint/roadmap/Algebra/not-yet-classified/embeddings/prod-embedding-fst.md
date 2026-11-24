# Prod Embedding Fst

Embedding `FGModuleCat R ⥤ FGModuleCat (R × S)` via `RingHom.fst`.

An `R`-module `M` is regarded as an `(R × S)`-module by `(r,s) • m = r • m`.
This is `restrictScalars` along `fst`, using that `fst` is finite.
