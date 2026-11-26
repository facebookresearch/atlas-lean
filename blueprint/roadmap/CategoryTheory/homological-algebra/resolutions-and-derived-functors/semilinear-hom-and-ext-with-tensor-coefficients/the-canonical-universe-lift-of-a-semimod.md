# Universe lift of semimodules and linear maps

For a semiring `R : Type ringU`, the functor `SemimoduleCat.{carrierU} R → SemimoduleCat.{max
liftU carrierU} R` sends `M` to `ULift.{liftU} M`, with the transported `R`-module structure.
It sends a linear map `f` to the map `ULift.up m ↦ ULift.up (f m)`.
