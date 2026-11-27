# Native module coefficients descend

The coefficient functor descends to the enhanced $\mathcal{D}$-module quotient. Let $X$ be a
Hausdorff complex manifold of dimension $n$, with the given interface data, among them the enhanced
module geometry `Geometry`, the boundary proper image `Boundary`, the base inverse image
`Projection`, and the exactness `ModuleExact` and boundedness `ModuleBounded` of forgetting the
module structure. Then the functor `moduleCoefficientQuotientInput`, from bounded objects of the
derived category of modules over `RY` (bimodules over `RY` and the trivial monoid `KY`) in
ind-sheaves on the ambient space of the enhanced space of $X$ to the enhanced category of
ind-sheaves, which forgets the module structure and then applies the enhanced quotient, inverts
every morphism whose cone lies in the smallest triangulated subcategory closed under isomorphisms
that contains the boundary proper images `nativeBoundaryImage` and the inverse images from the base
`nativeBaseInverse`.
