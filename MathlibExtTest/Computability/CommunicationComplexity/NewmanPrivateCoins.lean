/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Computability.CommunicationComplexity.NewmanPrivateCoins

/-!
# Tests for private-coin communication protocols

These protocols use two independent fair bits or a single fair bit held by Alice.
-/

namespace MathlibExtTest.Computability.CommunicationComplexity.NewmanPrivateCoins

open MathlibExt.Computability.CommunicationComplexity

/-- Only the pair of private bits `(true, true)` gives the wrong output. -/
example :
    let p : Protocol (Unit × Bool) (Unit × Bool) :=
      .alice Prod.snd (.output false) (.bob Prod.snd (.output false) (.output true))
    privateErrorProb p (fun _ _ => false) () () = 1 / 4 := by
  norm_num [privateErrorProb, Protocol.eval]
  decide

/-- Giving Bob a singleton coin space preserves the uniform probability on Alice's bits. -/
example :
    let p : Protocol (Unit × Bool) (Unit × Unit) :=
      .alice Prod.snd (.output false) (.output true)
    privateErrorProb p (fun _ _ => true) () () = 1 / 2 := by
  norm_num [privateErrorProb, Protocol.eval]
  decide

end MathlibExtTest.Computability.CommunicationComplexity.NewmanPrivateCoins
