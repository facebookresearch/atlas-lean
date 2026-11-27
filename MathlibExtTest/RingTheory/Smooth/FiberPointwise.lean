/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Smooth.FiberPointwise

@[expose] public section

universe u v

-- Consumer with the original binders.
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight :
      S →ₐ[R] p.Fiber S).toRingHom = q)
    [Algebra.IsSmoothAt p.ResidueField Q] :
    Algebra.IsSmoothAt R q :=
  Algebra.isSmoothAt_of_isSmoothAt_fiber p q Q hQ

-- Higher-universe consumer.
example {R S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight :
      S →ₐ[R] p.Fiber S).toRingHom = q)
    [Algebra.IsSmoothAt p.ResidueField Q] :
    Algebra.IsSmoothAt R q :=
  Algebra.isSmoothAt_of_isSmoothAt_fiber p q Q hQ

