/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortData

/-! Complete signed source octad rows, retaining every original incoming coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Each balanced original row retains all sixty-four signed coefficients in four exact chunks. -/
def generatedTwelfthIncomingOctadCacheWords (o : Fin 759) : Fin 4 → ℕ :=
  (if o.val < 379 then
    (if o.val < 189 then
      (if o.val < 94 then
        (if o.val < 47 then
          (if o.val < 23 then
            (if o.val < 11 then
              (if o.val < 5 then
                (if o.val < 2 then
                  (if o.val < 1 then
                    (fun _ => 0)
                  else
                    (fun _ => 0))
                else
                  (if o.val < 3 then
                    (fun _ => 0)
                  else
                    (if o.val < 4 then
                      (fun _ => 0)
                    else
                      ![
                        0x0,
                        0x7f8000000003fc00000000000,
                        0x10000000000000000000000000000000002,
                        0x0
                      ])))
              else
                (if o.val < 8 then
                  (if o.val < 6 then
                    ![
                      0x0,
                      0x3fc00000080000000000000,
                      0xff0000000000000000000000000000000002,
                      0x0
                    ]
                  else
                    (if o.val < 7 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 9 then
                    ![
                      0x3fc00007f80000000000000,
                      0x0,
                      0x80000000000400000000000,
                      0x0
                    ]
                  else
                    (if o.val < 10 then
                      ![
                        0x400007f80000000000000,
                        0x7f80000000000400000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x3fc00010000000000000000000000000,
                        0x0,
                        0x0,
                        0x400010000000000000000000000000
                      ]))))
            else
              (if o.val < 17 then
                (if o.val < 14 then
                  (if o.val < 12 then
                    ![
                      0x400000000000ff0000000000000000,
                      0x0,
                      0x0,
                      0x3fc00000000000ff0000000000000000
                    ]
                  else
                    (if o.val < 13 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 15 then
                    ![
                      0x1fe00000000000003fc00,
                      0x0,
                      0x0,
                      0x1fe000000000000000400
                    ]
                  else
                    (if o.val < 16 then
                      ![
                        0x1fe00003fc00,
                        0x0,
                        0x0,
                        0x1fe000000400
                      ]
                    else
                      (fun _ => 0))))
              else
                (if o.val < 20 then
                  (if o.val < 18 then
                    (fun _ => 0)
                  else
                    (if o.val < 19 then
                      ![
                        0x1fe000000000000000000,
                        0x0,
                        0x0,
                        0x2000000000000000000
                      ]
                    else
                      ![
                        0x1fe000000000000000000,
                        0x0,
                        0x0,
                        0x2000000000000000000
                      ]))
                else
                  (if o.val < 21 then
                    ![
                      0x1fe,
                      0x0,
                      0x0,
                      0x1fe
                    ]
                  else
                    (if o.val < 22 then
                      ![
                        0x10000000000000000000000000000000000,
                        0x0,
                        0x0,
                        0x10000000000000000000000000000000000
                      ]
                    else
                      ![
                        0x10000000000000000000000000,
                        0x0,
                        0x0,
                        0xff0000000000000000000000000
                      ])))))
          else
            (if o.val < 35 then
              (if o.val < 29 then
                (if o.val < 26 then
                  (if o.val < 24 then
                    ![
                      0xff0000000000000000000000000,
                      0x0,
                      0x0,
                      0x10000000000000000000000000
                    ]
                  else
                    (if o.val < 25 then
                      ![
                        0x1fe,
                        0x0,
                        0x0,
                        0x1fe
                      ]
                    else
                      ![
                        0xff0000000000000000000000000000000000,
                        0x0,
                        0x0,
                        0xff0000000000000000000000000000000000
                      ]))
                else
                  (if o.val < 27 then
                    ![
                      0x0,
                      0x2,
                      0x1fe,
                      0x0
                    ]
                  else
                    (if o.val < 28 then
                      ![
                        0x0,
                        0xff0000000000000000000000000000000000,
                        0x10000000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x7f80000000000000000000000000000000,
                        0x80000000000000000000000000000000,
                        0x0
                      ])))
              else
                (if o.val < 32 then
                  (if o.val < 30 then
                    ![
                      0x0,
                      0x7f80000000000000000000000000000000,
                      0x80000000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 31 then
                      ![
                        0x0,
                        0xff0000000000000000000000000000000000,
                        0x10000000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x1fe,
                        0x2,
                        0x0
                      ]))
                else
                  (if o.val < 33 then
                    ![
                      0x0,
                      0x80000,
                      0x7f80000,
                      0x0
                    ]
                  else
                    (if o.val < 34 then
                      ![
                        0x0,
                        0x7f80000,
                        0x80000,
                        0x0
                      ]
                    else
                      ![
                        0x80000000000000000000000000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000000000000000000000
                      ]))))
            else
              (if o.val < 41 then
                (if o.val < 38 then
                  (if o.val < 36 then
                    ![
                      0x7f80000000000000,
                      0x0,
                      0x0,
                      0x7f80000000000000
                    ]
                  else
                    (if o.val < 37 then
                      ![
                        0x7f80000000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000
                      ]
                    else
                      ![
                        0x400000000000000000000000000000,
                        0x0,
                        0x0,
                        0x3fc00000000000000000000000000000
                      ]))
                else
                  (if o.val < 39 then
                    ![
                      0x3fc00,
                      0x0,
                      0x0,
                      0x400
                    ]
                  else
                    (if o.val < 40 then
                      ![
                        0x400000000000,
                        0x0,
                        0x0,
                        0x400000000000
                      ]
                    else
                      ![
                        0x3fc00000000000,
                        0x0,
                        0x0,
                        0x3fc00000000000
                      ])))
              else
                (if o.val < 44 then
                  (if o.val < 42 then
                    ![
                      0x80000,
                      0x0,
                      0x0,
                      0x7f80000
                    ]
                  else
                    (if o.val < 43 then
                      ![
                        0x0,
                        0x3fc00000000000000000000,
                        0x400000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x80000,
                        0x7f80000,
                        0x0
                      ]))
                else
                  (if o.val < 45 then
                    ![
                      0x0,
                      0x400,
                      0x3fc00,
                      0x0
                    ]
                  else
                    (if o.val < 46 then
                      ![
                        0x0,
                        0x3fc00000000000000000000,
                        0x400000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x7f80000000000000,
                        0x80000000000000,
                        0x0
                      ]))))))
        else
          (if o.val < 70 then
            (if o.val < 58 then
              (if o.val < 52 then
                (if o.val < 49 then
                  (if o.val < 48 then
                    ![
                      0x0,
                      0x3fc00000000000000000000000000000,
                      0x400000000000000000000000000000,
                      0x0
                    ]
                  else
                    ![
                      0x0,
                      0x80000000000000000000000000000000,
                      0x7f80000000000000000000000000000000,
                      0x0
                    ])
                else
                  (if o.val < 50 then
                    ![
                      0x0,
                      0x80000000000000,
                      0x7f80000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 51 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 55 then
                  (if o.val < 53 then
                    (fun _ => 0)
                  else
                    (if o.val < 54 then
                      (fun _ => 0)
                    else
                      ![
                        0x400000000000000000000007f80000,
                        0x0,
                        0x0,
                        0x8000000000000000000000000003fc00
                      ]))
                else
                  (if o.val < 56 then
                    ![
                      0x400000000000000000000000080000,
                      0x0,
                      0x0,
                      0x80000000000000000000000000000400
                    ]
                  else
                    (if o.val < 57 then
                      ![
                        0x400000000000000000000007f80000,
                        0x0,
                        0x0,
                        0x8000000000000000000000000003fc00
                      ]
                    else
                      ![
                        0x3fc00000000000000000000007f80000,
                        0x0,
                        0x0,
                        0x7f8000000000000000000000000003fc00
                      ]))))
            else
              (if o.val < 64 then
                (if o.val < 61 then
                  (if o.val < 59 then
                    ![
                      0x80000000000000,
                      0x80000,
                      0x3fc00000000000000000000000000000,
                      0x400000000000000000000
                    ]
                  else
                    (if o.val < 60 then
                      ![
                        0x7f80000000000000000000000,
                        0x400000000000000000000000000000,
                        0x7f80000,
                        0x3fc00000000000
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 62 then
                    (fun _ => 0)
                  else
                    (if o.val < 63 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 67 then
                  (if o.val < 65 then
                    ![
                      0x400000000000000000000,
                      0x400,
                      0x7f80000000000000000000000000000000,
                      0x80000000000000
                    ]
                  else
                    (if o.val < 66 then
                      ![
                        0x400000000000,
                        0x7f80000000000000000000000000000000,
                        0x400,
                        0x80000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x400000000000,
                        0x3fc00000000000,
                        0x0
                      ]))
                else
                  (if o.val < 68 then
                    ![
                      0x0,
                      0xff0000000000000000000000000000000000,
                      0x10000000000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 69 then
                      ![
                        0x0,
                        0x2,
                        0x1fe,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x400000000000,
                        0x3fc00000000000,
                        0x0
                      ])))))
          else
            (if o.val < 82 then
              (if o.val < 76 then
                (if o.val < 73 then
                  (if o.val < 71 then
                    ![
                      0x0,
                      0x7f80000000000000000000000,
                      0x80000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 72 then
                      ![
                        0x0,
                        0x10000000,
                        0xff0000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x2000000000000000000000000000,
                        0x1fe000000000000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 74 then
                    ![
                      0x0,
                      0x80000000000000000000000,
                      0x7f80000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 75 then
                      ![
                        0x400000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000000000000
                      ]
                    else
                      ![
                        0x400000000000000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000
                      ])))
              else
                (if o.val < 79 then
                  (if o.val < 77 then
                    ![
                      0x10000000,
                      0x0,
                      0x0,
                      0x2000000000000000000000000000
                    ]
                  else
                    (if o.val < 78 then
                      ![
                        0x1fe,
                        0x0,
                        0x0,
                        0xff0000000000000000000000000000000000
                      ]
                    else
                      ![
                        0x10000000,
                        0x0,
                        0x0,
                        0x2000000000000000000000000000
                      ]))
                else
                  (if o.val < 80 then
                    ![
                      0x2,
                      0x0,
                      0x0,
                      0x10000000000000000000000000000000000
                    ]
                  else
                    (if o.val < 81 then
                      ![
                        0x7f80000000000000000000000,
                        0x0,
                        0x0,
                        0x400000000000
                      ]
                    else
                      ![
                        0x80000000000000,
                        0x0,
                        0x0,
                        0x3fc00000000000000000000
                      ]))))
            else
              (if o.val < 88 then
                (if o.val < 85 then
                  (if o.val < 83 then
                    ![
                      0x4000000000000000000000000001fe,
                      0x0,
                      0x0,
                      0x3fc000000000000000000000000001fe
                    ]
                  else
                    (if o.val < 84 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 86 then
                    ![
                      0x2000000000000000000000000400,
                      0x0,
                      0x0,
                      0x200000000000000000000003fc00
                    ]
                  else
                    (if o.val < 87 then
                      ![
                        0x5fe000000000000000000000000000,
                        0x0,
                        0x0,
                        0x3fdfe000000000000000000000000000
                      ]
                    else
                      (fun _ => 0))))
              else
                (if o.val < 91 then
                  (if o.val < 89 then
                    (fun _ => 0)
                  else
                    (if o.val < 90 then
                      ![
                        0x3fdfe,
                        0x0,
                        0x0,
                        0x5fe
                      ]
                    else
                      ![
                        0x400,
                        0x2000000000,
                        0x1fe000000000000000000,
                        0x3fc00000000000000000000000000000
                      ]))
                else
                  (if o.val < 92 then
                    ![
                      0x3fc00,
                      0x1fe000000000,
                      0x1fe000000000000000000,
                      0x3fc00000000000000000000000000000
                    ]
                  else
                    (if o.val < 93 then
                      ![
                        0x400,
                        0x1fe000000000,
                        0x2000000000000000000,
                        0x3fc00000000000000000000000000000
                      ]
                    else
                      ![
                        0x400,
                        0x2000000000,
                        0x2000000000000000000,
                        0x400000000000000000000000000000
                      ])))))))
      else
        (if o.val < 141 then
          (if o.val < 117 then
            (if o.val < 105 then
              (if o.val < 99 then
                (if o.val < 96 then
                  (if o.val < 95 then
                    ![
                      0x7f80000,
                      0x10000000000000004000000000,
                      0x10000000000000000,
                      0x80000000000000000000000000000000
                    ]
                  else
                    ![
                      0x3f800000000000000000000000080000,
                      0xff0000000000000000000000000,
                      0xff0000000000000000,
                      0x7f80000000000000000000000000000000
                    ])
                else
                  (if o.val < 97 then
                    ![
                      0x7f80000,
                      0xff00000000000001fc000000000,
                      0xff0000000000000000,
                      0x80000000000000000000000000000000
                    ]
                  else
                    (if o.val < 98 then
                      ![
                        0x80000,
                        0x10000000000000000000000000,
                        0x10000000000000000,
                        0x7f80000000000000000000000000000800
                      ]
                    else
                      ![
                        0x4000000000000000000000000001fe,
                        0x0,
                        0x0,
                        0x3fc000000000000000000000000001fe
                      ])))
              else
                (if o.val < 102 then
                  (if o.val < 100 then
                    (fun _ => 0)
                  else
                    (if o.val < 101 then
                      (fun _ => 0)
                    else
                      ![
                        0x2000000000000000000000000400,
                        0x0,
                        0x0,
                        0x200000000000000000000003fc00
                      ]))
                else
                  (if o.val < 103 then
                    ![
                      0x402,
                      0x0,
                      0x0,
                      0x3fc02
                    ]
                  else
                    (if o.val < 104 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))
            else
              (if o.val < 111 then
                (if o.val < 108 then
                  (if o.val < 106 then
                    ![
                      0x3fc02000000000000000000000000000,
                      0x0,
                      0x0,
                      0x402000000000000000000000000000
                    ]
                  else
                    (if o.val < 107 then
                      ![
                        0x1fe,
                        0x400000000000000000000,
                        0x3fc00000000000,
                        0x2000000000000000000000000000
                      ]
                    else
                      ![
                        0x1fe,
                        0x400000000000,
                        0x400000000000000000000,
                        0x1fe000000000000000000000000000
                      ]))
                else
                  (if o.val < 109 then
                    ![
                      0x1fe,
                      0x3fc00000000000,
                      0x400000000000000000000,
                      0x2000000000000000000000000000
                    ]
                  else
                    (if o.val < 110 then
                      ![
                        0x2,
                        0x3fc00000000000000000000,
                        0x3fc00000000000,
                        0x2000000000000000000000000000
                      ]
                    else
                      ![
                        0x10000000,
                        0x8000000003f800000000000,
                        0x80000000000000,
                        0xff0000000000000000000000000000000000
                      ])))
              else
                (if o.val < 114 then
                  (if o.val < 112 then
                    ![
                      0x4000000000000000000010000000,
                      0x80000000000000,
                      0x80000000000000000000000,
                      0xff0000000000000000000000000000000000
                    ]
                  else
                    (if o.val < 113 then
                      ![
                        0x10000000,
                        0x800007f80000000000000,
                        0x7f80000000000000000000000,
                        0xff0000000000000000000000000000000000
                      ]
                    else
                      ![
                        0x10000000,
                        0x7f80000000000000000000000,
                        0x7f80000000000000,
                        0xff00000000000000000000000000000001fc
                      ]))
                else
                  (if o.val < 115 then
                    ![
                      0x3fc00,
                      0x0,
                      0x0,
                      0x80000000000000000000000000000000
                    ]
                  else
                    (if o.val < 116 then
                      ![
                        0x7f80000,
                        0x0,
                        0x0,
                        0x400000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x10000000,
                        0x1fe000000000000000000000000000,
                        0x0
                      ])))))
          else
            (if o.val < 129 then
              (if o.val < 123 then
                (if o.val < 120 then
                  (if o.val < 118 then
                    ![
                      0x0,
                      0x10000000,
                      0x1fe000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 119 then
                      ![
                        0x0,
                        0xff0000000000000000000000000000000000,
                        0x2,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x10000000000000000000000000000000000,
                        0x1fe,
                        0x0
                      ]))
                else
                  (if o.val < 121 then
                    ![
                      0x80000,
                      0x0,
                      0x0,
                      0x3fc00000000000000000000000000000
                    ]
                  else
                    (if o.val < 122 then
                      ![
                        0x3fc00,
                        0x0,
                        0x0,
                        0x80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x80000,
                        0x0,
                        0x0,
                        0x7f80000
                      ])))
              else
                (if o.val < 126 then
                  (if o.val < 124 then
                    ![
                      0xff0000000000000000000000000,
                      0x0,
                      0x0,
                      0xff0000000000000000000000000
                    ]
                  else
                    (if o.val < 125 then
                      ![
                        0xff0000000000000000000000000,
                        0x0,
                        0x0,
                        0xff0000000000000000000000000
                      ]
                    else
                      ![
                        0x3fc00000000000000000000000000000,
                        0x0,
                        0x0,
                        0x400000000000000000000000000000
                      ]))
                else
                  (if o.val < 127 then
                    ![
                      0x7f80000000000000000000000000000000,
                      0x0,
                      0x0,
                      0x80000000000000000000000000000000
                    ]
                  else
                    (if o.val < 128 then
                      ![
                        0x2000000000,
                        0x0,
                        0x0,
                        0x2000000000
                      ]
                    else
                      ![
                        0x1fe000000000,
                        0x0,
                        0x0,
                        0x1fe000000000
                      ]))))
            else
              (if o.val < 135 then
                (if o.val < 132 then
                  (if o.val < 130 then
                    ![
                      0x3fc00,
                      0x0,
                      0x0,
                      0x400
                    ]
                  else
                    (if o.val < 131 then
                      ![
                        0x400000000000000000000000000000,
                        0x10000002000000000000000000000000000,
                        0xff00001fe000000000000000000000000000,
                        0x7f80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x80000000000000,
                        0xff0000002000000000,
                        0x100001fe000000000,
                        0x400000000000
                      ]))
                else
                  (if o.val < 133 then
                    ![
                      0x400,
                      0x10000002,
                      0xff00001fe,
                      0x7f80000
                    ]
                  else
                    (if o.val < 134 then
                      ![
                        0x7f80000000000000,
                        0x100001fe000000000,
                        0xff0000002000000000,
                        0x3fc00000000000
                      ]
                    else
                      ![
                        0x10000002000000000000000000,
                        0x80000000000000000000000,
                        0x3fc00000000000000000000,
                        0xff00001fe000000000000000000
                      ])))
              else
                (if o.val < 138 then
                  (if o.val < 136 then
                    ![
                      0x100001fe,
                      0x400,
                      0x7f80000,
                      0x100001fe
                    ]
                  else
                    (if o.val < 137 then
                      ![
                        0xff00001fe000000000,
                        0x7f80000000000000,
                        0x400000000000,
                        0x10000002000000000
                      ]
                    else
                      ![
                        0xff0000002000000000000000000000000000,
                        0x3fc00000000000000000000000000000,
                        0x80000000000000000000000000000000,
                        0xff0000002000000000000000000000000000
                      ]))
                else
                  (if o.val < 139 then
                    (fun _ => 0)
                  else
                    (if o.val < 140 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))))
        else
          (if o.val < 165 then
            (if o.val < 153 then
              (if o.val < 147 then
                (if o.val < 144 then
                  (if o.val < 142 then
                    (fun _ => 0)
                  else
                    (if o.val < 143 then
                      ![
                        0xff0000002000000000,
                        0xff00001fe,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xff0000002000000000000000000,
                        0x0,
                        0xff00001fe,
                        0x0
                      ]))
                else
                  (if o.val < 145 then
                    ![
                      0x0,
                      0x10000002000000000000000000000000000,
                      0x0,
                      0xff0000002000000000000000000
                    ]
                  else
                    (if o.val < 146 then
                      ![
                        0x0,
                        0x0,
                        0xff00001fe000000000000000000000000000,
                        0x100001fe000000000
                      ]
                    else
                      (fun _ => 0))))
              else
                (if o.val < 150 then
                  (if o.val < 148 then
                    (fun _ => 0)
                  else
                    (if o.val < 149 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 151 then
                    ![
                      0xff0000002000000000,
                      0x0,
                      0xff00001fe000000000,
                      0x0
                    ]
                  else
                    (if o.val < 152 then
                      ![
                        0x0,
                        0x0,
                        0xff00001fe000000000,
                        0x100001fe000000000000000000
                      ]
                    else
                      ![
                        0xff0000002000000000000000000,
                        0xff00001fe000000000000000000,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 159 then
                (if o.val < 156 then
                  (if o.val < 154 then
                    ![
                      0x0,
                      0x10000002000000000000000000,
                      0x0,
                      0xff0000002000000000
                    ]
                  else
                    (if o.val < 155 then
                      ![
                        0xff00001fe000000000,
                        0x0,
                        0x0,
                        0xff0000002
                      ]
                    else
                      ![
                        0x100001fe,
                        0x0,
                        0x0,
                        0xff00001fe000000000
                      ]))
                else
                  (if o.val < 157 then
                    ![
                      0x10000002ff0000002,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 158 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff00001feff0000002
                      ]
                    else
                      ![
                        0x10000402000000000000000000,
                        0x0,
                        0x0,
                        0xff003fdfe000000000
                      ])))
              else
                (if o.val < 162 then
                  (if o.val < 160 then
                    ![
                      0x0,
                      0xff0080002,
                      0xff0080002000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 161 then
                      ![
                        0x0,
                        0xff0080002,
                        0xff0080002000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x10000402000000000,
                        0x0,
                        0x0,
                        0xff003fdfe000000000000000000
                      ]))
                else
                  (if o.val < 163 then
                    ![
                      0x0,
                      0x10080002000000000,
                      0xff7f801fe000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 164 then
                      ![
                        0xff003fc02,
                        0x0,
                        0x0,
                        0x100005fe000000000000000000000000000
                      ]
                    else
                      ![
                        0x100005fe000000000000000000000000000,
                        0x0,
                        0x0,
                        0xff003fc02
                      ])))))
          else
            (if o.val < 177 then
              (if o.val < 171 then
                (if o.val < 168 then
                  (if o.val < 166 then
                    ![
                      0x0,
                      0x10080002000000000,
                      0xff7f801fe000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 167 then
                      ![
                        0xff00001fe000000000,
                        0x0,
                        0x0,
                        0xff0000002
                      ]
                    else
                      ![
                        0x100001fe,
                        0x0,
                        0x0,
                        0xff00001fe000000000
                      ]))
                else
                  (if o.val < 169 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x100000020100001fe
                    ]
                  else
                    (if o.val < 170 then
                      ![
                        0xff00001fe0100001fe,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xff00001fe000000000000000000000000000,
                        0x7f80000000000000000000000000000000,
                        0x3fc00000000000000000000000000000,
                        0xff00001fe000000000000000000000000000
                      ])))
              else
                (if o.val < 174 then
                  (if o.val < 172 then
                    ![
                      0x0,
                      0x7f80000000000000,
                      0x400000000000,
                      0x0
                    ]
                  else
                    (if o.val < 173 then
                      ![
                        0xff00001fe,
                        0x7f80000,
                        0x3fc00,
                        0xff00001fe
                      ]
                    else
                      ![
                        0x0,
                        0x80000000000000,
                        0x3fc00000000000,
                        0x0
                      ]))
                else
                  (if o.val < 175 then
                    ![
                      0x10000002,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 176 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x10000002000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x10000002000000000000000000000000000
                      ]))))
            else
              (if o.val < 183 then
                (if o.val < 180 then
                  (if o.val < 178 then
                    ![
                      0xff00001fe,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 179 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 181 then
                    (fun _ => 0)
                  else
                    (if o.val < 182 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 186 then
                  (if o.val < 184 then
                    (fun _ => 0)
                  else
                    (if o.val < 185 then
                      ![
                        0x7f80000,
                        0x10000402000000000000000000,
                        0x10000402000000000,
                        0x80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x80000,
                        0xff003fdfe000000000000000000,
                        0xff003fdfe000000000,
                        0x7f80000000000000000000000000000000
                      ]))
                else
                  (if o.val < 187 then
                    (fun _ => 0)
                  else
                    (if o.val < 188 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))))))
    else
      (if o.val < 284 then
        (if o.val < 236 then
          (if o.val < 212 then
            (if o.val < 200 then
              (if o.val < 194 then
                (if o.val < 191 then
                  (if o.val < 190 then
                    (fun _ => 0)
                  else
                    ![
                      0x0,
                      0xff00001fe000000000000000000,
                      0x0,
                      0x0
                    ])
                else
                  (if o.val < 192 then
                    ![
                      0x0,
                      0xff00001fe000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 193 then
                      ![
                        0x0,
                        0x10000002000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xff00001fe000000000,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 197 then
                  (if o.val < 195 then
                    (fun _ => 0)
                  else
                    (if o.val < 196 then
                      (fun _ => 0)
                    else
                      ![
                        0xff00001fe000000000000000000000000000,
                        0x3fc00007f80000000000000000000000,
                        0x7f80000000000400000000000000000000,
                        0xff00001fe000000000000000000000000000
                      ]))
                else
                  (if o.val < 198 then
                    ![
                      0xff00001fe000000000000000000000000000,
                      0x3fc00000080000000000000000000000,
                      0x7f8000000003fc00000000000000000000,
                      0xff00001fe000000000000000000000000000
                    ]
                  else
                    (if o.val < 199 then
                      ![
                        0x10000002,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x10000002000000000000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 206 then
                (if o.val < 203 then
                  (if o.val < 201 then
                    ![
                      0xff00001fe000000000000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 202 then
                      ![
                        0x10000002,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0xff00001fe000000000000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 204 then
                    ![
                      0x0,
                      0x0,
                      0xff00001fe000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 205 then
                      ![
                        0x0,
                        0x10000002,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xff00001fe,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 209 then
                  (if o.val < 207 then
                    ![
                      0xff7f801fe000000000000000000000000000,
                      0x0,
                      0x0,
                      0xff7f801fe
                    ]
                  else
                    (if o.val < 208 then
                      ![
                        0x0,
                        0x80000000000000,
                        0x7f80000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x7f80000000000000000000000,
                        0x80000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 210 then
                    ![
                      0x10080002,
                      0x0,
                      0x0,
                      0x10080002000000000000000000000000000
                    ]
                  else
                    (if o.val < 211 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))))
          else
            (if o.val < 224 then
              (if o.val < 218 then
                (if o.val < 215 then
                  (if o.val < 213 then
                    (fun _ => 0)
                  else
                    (if o.val < 214 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 216 then
                    (fun _ => 0)
                  else
                    (if o.val < 217 then
                      ![
                        0x805fe,
                        0x10000000000000000000000000,
                        0x10000000000000000,
                        0x7fbfc02000000000000000000000000000
                      ]
                    else
                      ![
                        0x805fe,
                        0x10000000000000000,
                        0x10000000000000000000000000,
                        0x7fbfc02000000000000000000000000000
                      ])))
              else
                (if o.val < 221 then
                  (if o.val < 219 then
                    ![
                      0x0,
                      0x0,
                      0x80400,
                      0x0
                    ]
                  else
                    (if o.val < 220 then
                      ![
                        0x0,
                        0x0,
                        0x7fbfc00,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x80400000000000000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 222 then
                    ![
                      0x0,
                      0x0,
                      0x80400000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 223 then
                      ![
                        0x80400000000000,
                        0x2000000000,
                        0x10000000000000000,
                        0x80400000000000
                      ]
                    else
                      ![
                        0x0,
                        0x2,
                        0x10000000,
                        0x0
                      ]))))
            else
              (if o.val < 230 then
                (if o.val < 227 then
                  (if o.val < 225 then
                    ![
                      0x80400000000000,
                      0x2000000000,
                      0x10000000000000000,
                      0x80400000000000
                    ]
                  else
                    (if o.val < 226 then
                      ![
                        0x0,
                        0x2000000000000000000000000000,
                        0x10000000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x80400000000000
                      ]))
                else
                  (if o.val < 228 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x80400000000000000000000
                    ]
                  else
                    (if o.val < 229 then
                      ![
                        0x7fbfc00000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x80400000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 233 then
                  (if o.val < 231 then
                    (fun _ => 0)
                  else
                    (if o.val < 232 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 234 then
                    (fun _ => 0)
                  else
                    (if o.val < 235 then
                      ![
                        0x0,
                        0x80402,
                        0x80402000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x1fe000000000,
                        0x0,
                        0x0,
                        0x1fe000000000000000000
                      ]))))))
        else
          (if o.val < 260 then
            (if o.val < 248 then
              (if o.val < 242 then
                (if o.val < 239 then
                  (if o.val < 237 then
                    ![
                      0x2000000000000000000,
                      0x0,
                      0x0,
                      0x2000000000
                    ]
                  else
                    (if o.val < 238 then
                      ![
                        0x0,
                        0x7fbfdfe,
                        0x7fbfdfe000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x7fbfc00
                      ]))
                else
                  (if o.val < 240 then
                    ![
                      0x7fbfc00000000000000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 241 then
                      ![
                        0x80400,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x7fbfc00000000000000000000000000000
                      ])))
              else
                (if o.val < 245 then
                  (if o.val < 243 then
                    (fun _ => 0)
                  else
                    (if o.val < 244 then
                      (fun _ => 0)
                    else
                      ![
                        0x1fe010000000000000000000000000,
                        0x80400000000000000000000000000000,
                        0x7fbfc00000000000000000000000000000,
                        0x10000000000000002000000000000000000
                      ]))
                else
                  (if o.val < 246 then
                    ![
                      0x1feff0000000000000000000000000,
                      0x80400000000000000000000000000000,
                      0x7fbfc00000000000000000000000000000,
                      0x100000000000001fe000000000000000000
                    ]
                  else
                    (if o.val < 247 then
                      ![
                        0x0,
                        0x0,
                        0x7fbfc00,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x80400,
                        0x0
                      ]))))
            else
              (if o.val < 254 then
                (if o.val < 251 then
                  (if o.val < 249 then
                    ![
                      0x0,
                      0x80400000000000000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 250 then
                      ![
                        0x0,
                        0x80400000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 252 then
                    ![
                      0x2ff0000000000000000000000000,
                      0x0,
                      0x0,
                      0xff7fbfc00007fbfdfe000000000000000000
                    ]
                  else
                    (if o.val < 253 then
                      ![
                        0xff7fbfc00007fbfdfe000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0xff7fbfc00007fbfdfe000000000000000000,
                        0x0
                      ])))
              else
                (if o.val < 257 then
                  (if o.val < 255 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080400000080402000000000000000000
                    ]
                  else
                    (if o.val < 256 then
                      ![
                        0x0,
                        0xff7fbfc00007fbfdfe000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 258 then
                    ![
                      0x10080400000080402000000000000000000,
                      0x0,
                      0x0,
                      0x2ff0000000000000000000000000
                    ]
                  else
                    (if o.val < 259 then
                      ![
                        0x0,
                        0x10080400000080402000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff7fbfc00007fbfdfe000000000000000000
                      ])))))
          else
            (if o.val < 272 then
              (if o.val < 266 then
                (if o.val < 263 then
                  (if o.val < 261 then
                    ![
                      0x10080400000080402000000000000000000,
                      0x0,
                      0x0,
                      0x2ff0000000000000000000000000
                    ]
                  else
                    (if o.val < 262 then
                      (fun _ => 0)
                    else
                      ![
                        0x1fe010000000000000000000000000,
                        0x0,
                        0x0,
                        0x10080400000080402000000000000000000
                      ]))
                else
                  (if o.val < 264 then
                    (fun _ => 0)
                  else
                    (if o.val < 265 then
                      ![
                        0x0,
                        0x0,
                        0xff7fbfc00007fbfdfe000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0xff7fbfc00007fbfdfe000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 269 then
                  (if o.val < 267 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080000000000000000000000
                    ]
                  else
                    (if o.val < 268 then
                      ![
                        0x0,
                        0x0,
                        0x80000000000000000000000000000000,
                        0x10000000000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x2000000000000000000,
                        0x400000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 270 then
                    ![
                      0x0,
                      0x0,
                      0x10080000000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 271 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x10080000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x10080000000000000,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 278 then
                (if o.val < 275 then
                  (if o.val < 273 then
                    ![
                      0x0,
                      0x0,
                      0x10000000000000000,
                      0x80000000000000
                    ]
                  else
                    (if o.val < 274 then
                      ![
                        0x0,
                        0x2000000000000000000000000000,
                        0x3fc00000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x10080000,
                        0x0,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 276 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0xff7f80000000000000000000000000000000
                    ]
                  else
                    (if o.val < 277 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 281 then
                  (if o.val < 279 then
                    (fun _ => 0)
                  else
                    (if o.val < 280 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 282 then
                    (fun _ => 0)
                  else
                    (if o.val < 283 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))))))
      else
        (if o.val < 331 then
          (if o.val < 307 then
            (if o.val < 295 then
              (if o.val < 289 then
                (if o.val < 286 then
                  (if o.val < 285 then
                    (fun _ => 0)
                  else
                    ![
                      0x80000000000000000000000010000000,
                      0xff7f80000,
                      0x10080000,
                      0x10000000000000000000000000007f80000
                    ])
                else
                  (if o.val < 287 then
                    (fun _ => 0)
                  else
                    (if o.val < 288 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 292 then
                  (if o.val < 290 then
                    (fun _ => 0)
                  else
                    (if o.val < 291 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 293 then
                    (fun _ => 0)
                  else
                    (if o.val < 294 then
                      ![
                        0x10000000000000000000000000007f80000,
                        0xff7f80000000000000000000000000000000,
                        0x10080000000000000000000000000000000,
                        0x7f80000000000000000000000ff0000000
                      ]
                    else
                      (fun _ => 0)))))
            else
              (if o.val < 301 then
                (if o.val < 298 then
                  (if o.val < 296 then
                    (fun _ => 0)
                  else
                    (if o.val < 297 then
                      ![
                        0x10080000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xff7f80000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 299 then
                    ![
                      0x0,
                      0x2000000000,
                      0x400000000000,
                      0x0
                    ]
                  else
                    (if o.val < 300 then
                      ![
                        0x80000,
                        0x10000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xff7f80000000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 304 then
                  (if o.val < 302 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080000000000000000000000000000000
                    ]
                  else
                    (if o.val < 303 then
                      ![
                        0x10080000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x2,
                        0x3fc00,
                        0x0
                      ]))
                else
                  (if o.val < 305 then
                    ![
                      0xff0000000000000000000000000,
                      0x7f80000000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 306 then
                      ![
                        0x0,
                        0x0,
                        0x10080000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0xff0000000000000000000000000000080000,
                        0x10080000000000000000000000000000000,
                        0xff7f80000000000000000000000000000000,
                        0x80000000000000000000000010000000
                      ])))))
          else
            (if o.val < 319 then
              (if o.val < 313 then
                (if o.val < 310 then
                  (if o.val < 308 then
                    (fun _ => 0)
                  else
                    (if o.val < 309 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 311 then
                    (fun _ => 0)
                  else
                    (if o.val < 312 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 316 then
                  (if o.val < 314 then
                    (fun _ => 0)
                  else
                    (if o.val < 315 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 317 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080000000000000000000000000000000
                    ]
                  else
                    (if o.val < 318 then
                      ![
                        0x10080000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x1fe,
                        0x400,
                        0x0
                      ]))))
            else
              (if o.val < 325 then
                (if o.val < 322 then
                  (if o.val < 320 then
                    ![
                      0xff0000000000000000000000000,
                      0x7f80000000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 321 then
                      ![
                        0x0,
                        0x0,
                        0x10080000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x7f80000,
                        0xff0000000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 323 then
                    ![
                      0x3fdfe000000000000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 324 then
                      ![
                        0x0,
                        0x0,
                        0x10080000,
                        0x0
                      ]
                    else
                      ![
                        0x10080000000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 328 then
                  (if o.val < 326 then
                    ![
                      0x0,
                      0x1fe000000000,
                      0x3fc00000000000,
                      0x0
                    ]
                  else
                    (if o.val < 327 then
                      ![
                        0x0,
                        0x0,
                        0x400000000000000000000,
                        0x2000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x402000000000000000000000000000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 329 then
                    ![
                      0x10080000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 330 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff7f80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x2000000000000000000000000000,
                        0x3fc00000000000000000000000000000,
                        0x0
                      ]))))))
        else
          (if o.val < 355 then
            (if o.val < 343 then
              (if o.val < 337 then
                (if o.val < 334 then
                  (if o.val < 332 then
                    ![
                      0x0,
                      0x0,
                      0x10080000000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 333 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff7f80000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x2000000000000000000,
                        0x400000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 335 then
                    ![
                      0x0,
                      0x0,
                      0x1fe,
                      0x3fc00
                    ]
                  else
                    (if o.val < 336 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x10080000000000000000000000
                      ]
                    else
                      ![
                        0x80000000000000000000000010000000,
                        0xff7f80000,
                        0x10080000,
                        0x10000000000000000000000000007f80000
                      ])))
              else
                (if o.val < 340 then
                  (if o.val < 338 then
                    (fun _ => 0)
                  else
                    (if o.val < 339 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 341 then
                    (fun _ => 0)
                  else
                    (if o.val < 342 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))
            else
              (if o.val < 349 then
                (if o.val < 346 then
                  (if o.val < 344 then
                    (fun _ => 0)
                  else
                    (if o.val < 345 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 347 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x3fdfe000000000
                    ]
                  else
                    (if o.val < 348 then
                      ![
                        0x3fc00000000000000000000000000000,
                        0x1fe000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x10080000000000000000000000,
                        0xff0000000000000000000000000,
                        0x7f80000000000000000000000,
                        0x10080000000000000000000000
                      ])))
              else
                (if o.val < 352 then
                  (if o.val < 350 then
                    ![
                      0x0,
                      0x0,
                      0x402000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 351 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x3fdfe000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x80000,
                        0xff0000000
                      ]))
                else
                  (if o.val < 353 then
                    ![
                      0xff0080000000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 354 then
                      ![
                        0x17f80000000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xff0080000,
                        0x0,
                        0x0
                      ])))))
          else
            (if o.val < 367 then
              (if o.val < 361 then
                (if o.val < 358 then
                  (if o.val < 356 then
                    ![
                      0x3fc00000000000000000000,
                      0x5fe000000000000000000,
                      0x3fc02000000000000000000,
                      0x1fe000000000000000000
                    ]
                  else
                    (if o.val < 357 then
                      ![
                        0x0,
                        0x3fc02000000000000000000,
                        0x402000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x1fe000000002000000000,
                        0x3fc0000003fc00000000000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 359 then
                    ![
                      0x17f80000000000000000000000000000000,
                      0x10000000000000000000000000000080000,
                      0x80000000000000000000000ff0000000,
                      0xff0080000000000000000000000000000000
                    ]
                  else
                    (if o.val < 360 then
                      ![
                        0x3fc02,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]
                    else
                      ![
                        0x3fdfe,
                        0x0,
                        0x0,
                        0x3fc02000000000000000000000000000
                      ])))
              else
                (if o.val < 364 then
                  (if o.val < 362 then
                    (fun _ => 0)
                  else
                    (if o.val < 363 then
                      ![
                        0x5fe000000000,
                        0x402,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x402000000000000000000,
                        0x0,
                        0x5fe,
                        0x0
                      ]))
                else
                  (if o.val < 365 then
                    ![
                      0x402000000000,
                      0x0,
                      0x0,
                      0x5fe000000000000000000
                    ]
                  else
                    (if o.val < 366 then
                      ![
                        0x3fc00,
                        0x1fe,
                        0x10000000,
                        0x7f80000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x80000007f80000000000000,
                        0x10000000010000000000000000
                      ]))))
            else
              (if o.val < 373 then
                (if o.val < 370 then
                  (if o.val < 368 then
                    ![
                      0x0,
                      0x3fdfe000000000,
                      0x3fc02000000000,
                      0x0
                    ]
                  else
                    (if o.val < 369 then
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x5fe000000000000000000000000000
                      ]
                    else
                      ![
                        0x5fe,
                        0x0,
                        0x0,
                        0x3fdfe000000000000000000000000000
                      ]))
                else
                  (if o.val < 371 then
                    ![
                      0x17f80000,
                      0x7f80000000000000000000000010000000,
                      0x10000000000000000000000000000080000,
                      0xff0080000
                    ]
                  else
                    (if o.val < 372 then
                      ![
                        0x0,
                        0x3fc02000000000000000000000000000,
                        0x402000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x402000000000000000000000000000,
                        0x3fc02000000000000000000
                      ])))
              else
                (if o.val < 376 then
                  (if o.val < 374 then
                    (fun _ => 0)
                  else
                    (if o.val < 375 then
                      ![
                        0x400,
                        0x1fe,
                        0xff0000000,
                        0x7f80000
                      ]
                    else
                      ![
                        0x3fc02000000000,
                        0x0,
                        0x0,
                        0x402000000000000000000
                      ]))
                else
                  (if o.val < 377 then
                    ![
                      0x402000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 378 then
                      ![
                        0x0,
                        0x402,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xff7f80000000000000,
                        0x10000000000000000,
                        0x80000000000000,
                        0xff7f80000000000000
                      ])))))))))
  else
    (if o.val < 569 then
      (if o.val < 474 then
        (if o.val < 426 then
          (if o.val < 402 then
            (if o.val < 390 then
              (if o.val < 384 then
                (if o.val < 381 then
                  (if o.val < 380 then
                    ![
                      0x0,
                      0x0,
                      0x400,
                      0x2
                    ]
                  else
                    ![
                      0x3fdfe000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ])
                else
                  (if o.val < 382 then
                    ![
                      0x400000000000,
                      0x3fc02000000000,
                      0x5fe000000000,
                      0x2000000000
                    ]
                  else
                    (if o.val < 383 then
                      ![
                        0x0,
                        0x17f80000000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x17f80000000000000
                      ])))
              else
                (if o.val < 387 then
                  (if o.val < 385 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x17f80000000000000
                    ]
                  else
                    (if o.val < 386 then
                      ![
                        0x80000000000000000000000000000000,
                        0xff0000000000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x402000000000000000000000000000,
                        0x0,
                        0x3fc02000000000000000000
                      ]))
                else
                  (if o.val < 388 then
                    ![
                      0x0,
                      0x3fc02000000000000000000000000000,
                      0x0,
                      0x402000000000
                    ]
                  else
                    (if o.val < 389 then
                      (fun _ => 0)
                    else
                      ![
                        0x3fc00,
                        0x2,
                        0x400000000000000000000000000000,
                        0x2000000000000000000000000000
                      ]))))
            else
              (if o.val < 396 then
                (if o.val < 393 then
                  (if o.val < 391 then
                    ![
                      0x5fe000000000,
                      0x0,
                      0x0,
                      0xff7f80000
                    ]
                  else
                    (if o.val < 392 then
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x5fe000000000000000000000000000
                      ]
                    else
                      ![
                        0x3fc02,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]))
                else
                  (if o.val < 394 then
                    ![
                      0x17f80000,
                      0x7f80000000000000000000000010000000,
                      0x10000000000000000000000000000080000,
                      0xff0080000
                    ]
                  else
                    (if o.val < 395 then
                      ![
                        0x0,
                        0x0,
                        0x2000000002000000000,
                        0x3fc00000000400000000000
                      ]
                    else
                      ![
                        0x0,
                        0x402000000000,
                        0x5fe000000000,
                        0x0
                      ])))
              else
                (if o.val < 399 then
                  (if o.val < 397 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x3fc02000000000000000000000000000
                    ]
                  else
                    (if o.val < 398 then
                      ![
                        0x80000000000000000000000000000000,
                        0xff0000000000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x400000000000,
                        0x3fc02000000000,
                        0x5fe000000000,
                        0x2000000000
                      ]))
                else
                  (if o.val < 400 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0xff0080000000000000000000000
                    ]
                  else
                    (if o.val < 401 then
                      ![
                        0x0,
                        0x0,
                        0x17f80000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x402000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))))
          else
            (if o.val < 414 then
              (if o.val < 408 then
                (if o.val < 405 then
                  (if o.val < 403 then
                    ![
                      0x402000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 404 then
                      ![
                        0x10080000000000000,
                        0xff0000000000000000,
                        0x7f80000000000000,
                        0x10080000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x10000000000000000000000000000000000,
                        0x80000000000000000000000000000000
                      ]))
                else
                  (if o.val < 406 then
                    ![
                      0xff7f80000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 407 then
                      ![
                        0x400000000000000000000,
                        0x3fc02000000000000000000,
                        0x5fe000000000000000000,
                        0x2000000000000000000
                      ]
                    else
                      ![
                        0x17f80000000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 411 then
                  (if o.val < 409 then
                    ![
                      0x0,
                      0x17f80000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 410 then
                      ![
                        0x17f80000000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x1fe000000000000000000000000000,
                        0x400000000000000000000000000000
                      ]))
                else
                  (if o.val < 412 then
                    ![
                      0x3fc00000000000000000000000000000,
                      0x1fe000000000000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 413 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x3fdfe000000000
                      ]
                    else
                      ![
                        0x0,
                        0x402000000000000000000000000000,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 420 then
                (if o.val < 417 then
                  (if o.val < 415 then
                    ![
                      0x0,
                      0x0,
                      0x3fdfe000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 416 then
                      ![
                        0x10080000000000000000000000,
                        0xff0000000000000000000000000,
                        0x7f80000000000000000000000,
                        0x10080000000000000000000000
                      ]
                    else
                      ![
                        0x402000000000,
                        0x0,
                        0x5fe,
                        0x0
                      ]))
                else
                  (if o.val < 418 then
                    ![
                      0x4020000005fe000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 419 then
                      (fun _ => 0)
                    else
                      ![
                        0x400,
                        0x2,
                        0x400000000000000000000000000000,
                        0x1fe000000000000000000000000000
                      ])))
              else
                (if o.val < 423 then
                  (if o.val < 421 then
                    ![
                      0x3fdfe000000000,
                      0x0,
                      0x0,
                      0xff0080000
                    ]
                  else
                    (if o.val < 422 then
                      ![
                        0x3fc02,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]
                    else
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x5fe000000000000000000000000000
                      ]))
                else
                  (if o.val < 424 then
                    ![
                      0xff0080000000000000000000000000000000,
                      0xff0000000000000000000000000007f80000,
                      0x7f80000000000000000000000010000000,
                      0x17f80000000000000000000000000000000
                    ]
                  else
                    (if o.val < 425 then
                      ![
                        0x1fe000000002000000000,
                        0x3fc0000003fc00000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x17f80000,
                        0xff7f80000,
                        0x0
                      ]))))))
        else
          (if o.val < 450 then
            (if o.val < 438 then
              (if o.val < 432 then
                (if o.val < 429 then
                  (if o.val < 427 then
                    ![
                      0x0,
                      0x3fc02000000000,
                      0x402000000000,
                      0x0
                    ]
                  else
                    (if o.val < 428 then
                      ![
                        0x0,
                        0x0,
                        0x7f80000007f80000000000000,
                        0x10000000ff0000000000000000
                      ]
                    else
                      ![
                        0x17f80000,
                        0xff0000000000000000000000000000080000,
                        0x7f80000000000000000000000ff0000000,
                        0x17f80000
                      ]))
                else
                  (if o.val < 430 then
                    ![
                      0x3fc02000000000000000000000000000,
                      0x0,
                      0x0,
                      0x3fdfe
                    ]
                  else
                    (if o.val < 431 then
                      ![
                        0x0,
                        0x3fc02000000000,
                        0x402000000000000000000,
                        0x0
                      ]
                    else
                      (fun _ => 0))))
              else
                (if o.val < 435 then
                  (if o.val < 433 then
                    ![
                      0x0,
                      0x0,
                      0x3fc02000000000000000000000000000,
                      0x402000000000000000000
                    ]
                  else
                    (if o.val < 434 then
                      ![
                        0x0,
                        0x3fdfe000000000000000000000000000,
                        0x5fe000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x3fdfe000000000000000000,
                        0x0,
                        0x0,
                        0x5fe000000000
                      ]))
                else
                  (if o.val < 436 then
                    ![
                      0x400000000000000000000000000000,
                      0x1fe000000000000000000000000000,
                      0xff0000000000000000000000000000000000,
                      0x7f80000000000000000000000000000000
                    ]
                  else
                    (if o.val < 437 then
                      ![
                        0x0,
                        0x0,
                        0x10000000000000000,
                        0x80000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x10080000000000000,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 444 then
                (if o.val < 441 then
                  (if o.val < 439 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080000000000000000000000000000000
                    ]
                  else
                    (if o.val < 440 then
                      ![
                        0x10080000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x1fe,
                        0x3fc02,
                        0x5fe,
                        0x3fc00
                      ]))
                else
                  (if o.val < 442 then
                    ![
                      0x0,
                      0x402000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 443 then
                      ![
                        0x2000000000,
                        0x400000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xff0080000000000000000000000000000000,
                        0x7f80000000000000000000000000000000,
                        0x10000000000000000000000000000000000,
                        0xff0080000000000000000000000000000000
                      ])))
              else
                (if o.val < 447 then
                  (if o.val < 445 then
                    ![
                      0x402,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 446 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]
                    else
                      ![
                        0x1fe000000000000000000000000000,
                        0x3fc02000000000000000000000000000,
                        0x5fe000000000000000000000000000,
                        0x3fc00000000000000000000000000000
                      ]))
                else
                  (if o.val < 448 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080000000000000000000000000000000
                    ]
                  else
                    (if o.val < 449 then
                      ![
                        0xff7f80000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0xff7f80000000000000000000000,
                        0x0
                      ])))))
          else
            (if o.val < 462 then
              (if o.val < 456 then
                (if o.val < 453 then
                  (if o.val < 451 then
                    ![
                      0x10000000000000000000000000,
                      0x80000000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 452 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x3fdfe000000000000000000000000000
                      ]
                    else
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 454 then
                    ![
                      0x17f80000,
                      0x80000,
                      0xff0000000,
                      0x17f80000
                    ]
                  else
                    (if o.val < 455 then
                      ![
                        0x0,
                        0x0,
                        0x2000000000000000000,
                        0x400000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x3fdfe000000000,
                        0x0
                      ])))
              else
                (if o.val < 459 then
                  (if o.val < 457 then
                    ![
                      0x2000000002000000000,
                      0x3fc00000000400000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 458 then
                      ![
                        0x0,
                        0x3fdfe000000000000000000,
                        0x3fc02000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x5fe000000000000000000,
                        0x3fdfe000000000,
                        0x0
                      ]))
                else
                  (if o.val < 460 then
                    ![
                      0x0,
                      0x402000000000000000000,
                      0x5fe000000000,
                      0x0
                    ]
                  else
                    (if o.val < 461 then
                      ![
                        0xff0080000000000000000000000000000000,
                        0x7f80000000000000000000000ff0000000,
                        0x10000000000000000000000000007f80000,
                        0xff0080000000000000000000000000000000
                      ]
                    else
                      ![
                        0x3fc02000000000000000000,
                        0x0,
                        0x3fdfe,
                        0x0
                      ]))))
            else
              (if o.val < 468 then
                (if o.val < 465 then
                  (if o.val < 463 then
                    ![
                      0x402000000000,
                      0x5fe,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 464 then
                      (fun _ => 0)
                    else
                      ![
                        0x3fc00000000000000000000000000000,
                        0x1fe000000000000000000000000000,
                        0x10000000000000000000000000000000000,
                        0x7f80000000000000000000000000000000
                      ]))
                else
                  (if o.val < 466 then
                    ![
                      0x3fc02000000000000000000,
                      0x0,
                      0x0,
                      0x3fdfe000000000
                    ]
                  else
                    (if o.val < 467 then
                      ![
                        0x0,
                        0x0,
                        0x80000000000000,
                        0x10000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x402000000000,
                        0x0
                      ])))
              else
                (if o.val < 471 then
                  (if o.val < 469 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x3fdfe000000000000000000000000000
                    ]
                  else
                    (if o.val < 470 then
                      ![
                        0x3fdfe,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x17f80000,
                        0x80000,
                        0xff0000000,
                        0x17f80000
                      ]))
                else
                  (if o.val < 472 then
                    ![
                      0x2000000000000000000000000000,
                      0x5fe000000000000000000000000000,
                      0x3fc02000000000000000000000000000,
                      0x400000000000000000000000000000
                    ]
                  else
                    (if o.val < 473 then
                      ![
                        0x10080000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff7f80000000000000000000000000000000
                      ])))))))
      else
        (if o.val < 521 then
          (if o.val < 497 then
            (if o.val < 485 then
              (if o.val < 479 then
                (if o.val < 476 then
                  (if o.val < 475 then
                    ![
                      0x0,
                      0x0,
                      0xff7f80000000000000000000000,
                      0x0
                    ]
                  else
                    ![
                      0x10000000000000000000000000,
                      0x80000000000000000000000,
                      0x0,
                      0x0
                    ])
                else
                  (if o.val < 477 then
                    ![
                      0x3fc02000000000,
                      0x0,
                      0x3fdfe,
                      0x0
                    ]
                  else
                    (if o.val < 478 then
                      ![
                        0x5fe000000402000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      (fun _ => 0))))
              else
                (if o.val < 482 then
                  (if o.val < 480 then
                    ![
                      0x3fc00000000000000000000000000000,
                      0x1fe000000000000000000000000000,
                      0x3fc00,
                      0x2
                    ]
                  else
                    (if o.val < 481 then
                      ![
                        0xff0080000,
                        0x0,
                        0x0,
                        0x3fdfe000000000
                      ]
                    else
                      ![
                        0x0,
                        0x402000000000,
                        0x5fe000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 483 then
                    ![
                      0x0,
                      0x402000000000,
                      0x3fc02000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 484 then
                      ![
                        0x17f80000000000000000000000000000000,
                        0x80000000000000000000000010000000,
                        0xff0000000000000000000000000000080000,
                        0x17f80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x1fe0000001fe000000000,
                        0x40000003fc00000000000,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 491 then
                (if o.val < 488 then
                  (if o.val < 486 then
                    ![
                      0x0,
                      0xff7f80000,
                      0xff0080000,
                      0x0
                    ]
                  else
                    (if o.val < 487 then
                      ![
                        0x0,
                        0x3fc02000000000000000000000000000,
                        0x0,
                        0x402000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x3fdfe000000000000000000000000000,
                        0x0,
                        0x5fe000000000
                      ]))
                else
                  (if o.val < 489 then
                    (fun _ => 0)
                  else
                    (if o.val < 490 then
                      ![
                        0x400000000000000000000000000000,
                        0x1fe000000000000000000000000000,
                        0x3fc00,
                        0x1fe
                      ]
                    else
                      ![
                        0xff7f80000,
                        0x0,
                        0x0,
                        0x5fe000000000
                      ])))
              else
                (if o.val < 494 then
                  (if o.val < 492 then
                    ![
                      0x3fc02000000000000000000000000000,
                      0x0,
                      0x0,
                      0x402
                    ]
                  else
                    (if o.val < 493 then
                      ![
                        0x0,
                        0x5fe000000000,
                        0x402000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x17f80000,
                        0xff0000000000000000000000000000080000,
                        0x7f80000000000000000000000ff0000000,
                        0x17f80000
                      ]))
                else
                  (if o.val < 495 then
                    ![
                      0x0,
                      0x0,
                      0x20000001fe000000000,
                      0x400000000400000000000
                    ]
                  else
                    (if o.val < 496 then
                      ![
                        0x0,
                        0x3fc02000000000,
                        0x402000000000,
                        0x0
                      ]
                    else
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x0
                      ])))))
          else
            (if o.val < 509 then
              (if o.val < 503 then
                (if o.val < 500 then
                  (if o.val < 498 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x3fdfe000000000000000000000000000
                    ]
                  else
                    (if o.val < 499 then
                      ![
                        0x17f80000000000000000000000000000000,
                        0x80000000000000000000000000000000,
                        0xff0000000000000000000000000000000000,
                        0x17f80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x2000000000,
                        0x400000000000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 501 then
                    ![
                      0x0,
                      0xff7f80000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 502 then
                      ![
                        0x0,
                        0x402000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x400000000000000000000,
                        0x2000000000000000000
                      ])))
              else
                (if o.val < 506 then
                  (if o.val < 504 then
                    ![
                      0x1fe,
                      0x3fc02,
                      0x5fe,
                      0x3fc00
                    ]
                  else
                    (if o.val < 505 then
                      ![
                        0xff7f80000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff7f80000000000000000000000000000000
                      ]))
                else
                  (if o.val < 507 then
                    (fun _ => 0)
                  else
                    (if o.val < 508 then
                      (fun _ => 0)
                    else
                      ![
                        0x7f80000000000400000080000007f80000,
                        0xff0000002000000000000000000,
                        0x100001fe000000000ff00001feff00001fe,
                        0x7f80000000000400007f80000000080000
                      ]))))
            else
              (if o.val < 515 then
                (if o.val < 512 then
                  (if o.val < 510 then
                    (fun _ => 0)
                  else
                    (if o.val < 511 then
                      (fun _ => 0)
                    else
                      ![
                        0x400000000000,
                        0x0,
                        0x0,
                        0x80000000000000
                      ]))
                else
                  (if o.val < 513 then
                    ![
                      0x80000000000000000000000000000000,
                      0x0,
                      0x0,
                      0x3fc00000000000000000000000000000
                    ]
                  else
                    (if o.val < 514 then
                      ![
                        0x3fc00000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000
                      ]
                    else
                      ![
                        0x80000,
                        0x0,
                        0x0,
                        0x3fc00
                      ])))
              else
                (if o.val < 518 then
                  (if o.val < 516 then
                    ![
                      0x0,
                      0x7f80000,
                      0x400,
                      0x0
                    ]
                  else
                    (if o.val < 517 then
                      ![
                        0x0,
                        0x3fc00000000000000000000,
                        0x80000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x80000000000000000000000000000000,
                        0x3fc00000000000000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 519 then
                    ![
                      0x0,
                      0x400000000000,
                      0x7f80000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 520 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))))
        else
          (if o.val < 545 then
            (if o.val < 533 then
              (if o.val < 527 then
                (if o.val < 524 then
                  (if o.val < 522 then
                    (fun _ => 0)
                  else
                    (if o.val < 523 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 525 then
                    (fun _ => 0)
                  else
                    (if o.val < 526 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 530 then
                  (if o.val < 528 then
                    (fun _ => 0)
                  else
                    (if o.val < 529 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 531 then
                    (fun _ => 0)
                  else
                    (if o.val < 532 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))
            else
              (if o.val < 539 then
                (if o.val < 536 then
                  (if o.val < 534 then
                    (fun _ => 0)
                  else
                    (if o.val < 535 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 537 then
                    (fun _ => 0)
                  else
                    (if o.val < 538 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 542 then
                  (if o.val < 540 then
                    ![
                      0x0,
                      0x400,
                      0x400000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 541 then
                      ![
                        0x80000000000000000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000
                      ]
                    else
                      ![
                        0x80000000000000,
                        0x0,
                        0x0,
                        0x7f80000000000000000000000
                      ]))
                else
                  (if o.val < 543 then
                    ![
                      0x0,
                      0x400,
                      0x400000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 544 then
                      ![
                        0x80000,
                        0x0,
                        0x0,
                        0x7f80000000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x3fc00000000000,
                        0x400000000000000000000,
                        0x0
                      ])))))
          else
            (if o.val < 557 then
              (if o.val < 551 then
                (if o.val < 548 then
                  (if o.val < 546 then
                    ![
                      0x0,
                      0x3fc00000000000,
                      0x400000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 547 then
                      ![
                        0x7f80000000000000000000000000000000,
                        0x0,
                        0x0,
                        0x80000
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 549 then
                    (fun _ => 0)
                  else
                    (if o.val < 550 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 554 then
                  (if o.val < 552 then
                    ![
                      0xff00001fe000000000,
                      0x3fc00000000000,
                      0x80000000000000,
                      0x10000002000000000
                    ]
                  else
                    (if o.val < 553 then
                      ![
                        0x0,
                        0x400000000000000000000000000000,
                        0x80000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x10000002000000000,
                        0x400000000000,
                        0x7f80000000000000,
                        0xff00001fe000000000
                      ]))
                else
                  (if o.val < 555 then
                    ![
                      0x0,
                      0x400,
                      0x80000,
                      0x0
                    ]
                  else
                    (if o.val < 556 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff00001fe000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x10000002000000000
                      ]))))
            else
              (if o.val < 563 then
                (if o.val < 560 then
                  (if o.val < 558 then
                    ![
                      0xff00001fe000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 559 then
                      ![
                        0xff00001fe000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 561 then
                    (fun _ => 0)
                  else
                    (if o.val < 562 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 566 then
                  (if o.val < 564 then
                    ![
                      0xff003fdfe,
                      0x80000000000000000000000,
                      0x80000000000000,
                      0x10000402000000000000000000000000000
                    ]
                  else
                    (if o.val < 565 then
                      ![
                        0x10000402,
                        0x7f80000000000000000000000,
                        0x7f80000000000000,
                        0xff003fdfe000000000000000000000000000
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 567 then
                    (fun _ => 0)
                  else
                    (if o.val < 568 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))))))
    else
      (if o.val < 664 then
        (if o.val < 616 then
          (if o.val < 592 then
            (if o.val < 580 then
              (if o.val < 574 then
                (if o.val < 571 then
                  (if o.val < 570 then
                    (fun _ => 0)
                  else
                    (fun _ => 0))
                else
                  (if o.val < 572 then
                    ![
                      0x10000002000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 573 then
                      ![
                        0x10000002000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff00001fe000000000
                      ])))
              else
                (if o.val < 577 then
                  (if o.val < 575 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10000002000000000000000000
                    ]
                  else
                    (if o.val < 576 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 578 then
                    ![
                      0x10000002000000000000000000,
                      0x7f80000000000400000000000000000000,
                      0x3fc00007f80000000000000000000000,
                      0xff00001fe000000000000000000
                    ]
                  else
                    (if o.val < 579 then
                      ![
                        0xff00001fe000000000000000000,
                        0x7f8000000003fc00000000000000000000,
                        0x3fc00000080000000000000000000000,
                        0x10000002000000000000000000
                      ]
                    else
                      ![
                        0xff00001fe000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 586 then
                (if o.val < 583 then
                  (if o.val < 581 then
                    ![
                      0x10000002000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 582 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff00001fe000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xff00001fe000000000000000000
                      ]))
                else
                  (if o.val < 584 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0xff00001fe000000000000000000
                    ]
                  else
                    (if o.val < 585 then
                      ![
                        0xff00001fe000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x10000002000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 589 then
                  (if o.val < 587 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0xff00001fe000000000
                    ]
                  else
                    (if o.val < 588 then
                      ![
                        0x0,
                        0x10000402000000000,
                        0xff003fdfe000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x400000000000000000000000000000,
                        0x0,
                        0x0,
                        0x400
                      ]))
                else
                  (if o.val < 590 then
                    ![
                      0x3fc00,
                      0x0,
                      0x0,
                      0x3fc00000000000000000000000000000
                    ]
                  else
                    (if o.val < 591 then
                      ![
                        0x0,
                        0xff003fdfe000000000000000000,
                        0x10000402000000000,
                        0x0
                      ]
                    else
                      (fun _ => 0))))))
          else
            (if o.val < 604 then
              (if o.val < 598 then
                (if o.val < 595 then
                  (if o.val < 593 then
                    (fun _ => 0)
                  else
                    (if o.val < 594 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 596 then
                    ![
                      0xff0000000,
                      0x7f805fe000000000000000000,
                      0x7f805fe000000000,
                      0x10000000000000000000000000000000000
                    ]
                  else
                    (if o.val < 597 then
                      ![
                        0xff0000000,
                        0x7f805fe000000000,
                        0x7f805fe000000000000000000,
                        0x10000000000000000000000000000000000
                      ]
                    else
                      (fun _ => 0))))
              else
                (if o.val < 601 then
                  (if o.val < 599 then
                    (fun _ => 0)
                  else
                    (if o.val < 600 then
                      ![
                        0xbfc00,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xbfc00000000000000000000000000000
                      ]))
                else
                  (if o.val < 602 then
                    ![
                      0x7f80400,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 603 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0xbfc00000000000000000000000000000
                      ]
                    else
                      ![
                        0xbfc00,
                        0x10000000,
                        0x2,
                        0x7f80400
                      ]))))
            else
              (if o.val < 610 then
                (if o.val < 607 then
                  (if o.val < 605 then
                    ![
                      0x0,
                      0x10000000000000000,
                      0x2000000000,
                      0x0
                    ]
                  else
                    (if o.val < 606 then
                      ![
                        0xbfc00000000000000000000000000000,
                        0x10000000000000000000000000000000000,
                        0x2000000000000000000000000000,
                        0x7f80400000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x10000000000000000,
                        0x2000000000,
                        0x0
                      ]))
                else
                  (if o.val < 608 then
                    ![
                      0x0,
                      0xbfc00000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 609 then
                      ![
                        0x0,
                        0xbfc00000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xbfc00000000000000000000,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 613 then
                  (if o.val < 611 then
                    ![
                      0x0,
                      0x7f80400000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 612 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 614 then
                    (fun _ => 0)
                  else
                    (if o.val < 615 then
                      (fun _ => 0)
                    else
                      ![
                        0xff7f80400000000000,
                        0x0,
                        0x0,
                        0xff7f80400000000000000000000
                      ]))))))
        else
          (if o.val < 640 then
            (if o.val < 628 then
              (if o.val < 622 then
                (if o.val < 619 then
                  (if o.val < 617 then
                    ![
                      0x0,
                      0x10000000,
                      0x10000000000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 618 then
                      ![
                        0x0,
                        0xff0000000,
                        0xff0000000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x100bfc00000000000000000000,
                        0x0,
                        0x0,
                        0x100bfc00000000000
                      ]))
                else
                  (if o.val < 620 then
                    ![
                      0x0,
                      0xbfc00000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 621 then
                      ![
                        0x0,
                        0xbfc00000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x7f80400000000000000000000,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 625 then
                  (if o.val < 623 then
                    ![
                      0x0,
                      0xbfc00000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 624 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 626 then
                    ![
                      0xff0000000000000002000000000000000000,
                      0xbfc00000000000000000000,
                      0x7f80400000000000000000000,
                      0x2010000000000000000000000000
                    ]
                  else
                    (if o.val < 627 then
                      ![
                        0xff00000000000001fe000000000000000000,
                        0x7f80400000000000000000000,
                        0xbfc00000000000000000000,
                        0x2ff0000000000000000000000000
                      ]
                    else
                      ![
                        0x7f80400000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 634 then
                (if o.val < 631 then
                  (if o.val < 629 then
                    ![
                      0xbfc00000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 630 then
                      ![
                        0xbfc00000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xbfc00000000000,
                        0x0,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 632 then
                    (fun _ => 0)
                  else
                    (if o.val < 633 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 637 then
                  (if o.val < 635 then
                    (fun _ => 0)
                  else
                    (if o.val < 636 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 638 then
                    (fun _ => 0)
                  else
                    (if o.val < 639 then
                      ![
                        0xff0080000,
                        0x10000000000000000000000000007f80000,
                        0x80000000000000000000000010000000,
                        0xff0080000
                      ]
                    else
                      (fun _ => 0))))))
          else
            (if o.val < 652 then
              (if o.val < 646 then
                (if o.val < 643 then
                  (if o.val < 641 then
                    (fun _ => 0)
                  else
                    (if o.val < 642 then
                      ![
                        0x0,
                        0x3fdfe000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x1fe000000000,
                        0x3fc00000000000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 644 then
                    ![
                      0x0,
                      0x10000000,
                      0x80000,
                      0x0
                    ]
                  else
                    (if o.val < 645 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]
                    else
                      ![
                        0x3fdfe,
                        0x0,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 649 then
                  (if o.val < 647 then
                    ![
                      0x5fe000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 648 then
                      ![
                        0x400,
                        0x1fe,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xff0000000000000000000000000,
                        0x7f80000000000000000000000,
                        0x0
                      ]))
                else
                  (if o.val < 650 then
                    ![
                      0x5fe000000000000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 651 then
                      ![
                        0x5fe000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]))))
            else
              (if o.val < 658 then
                (if o.val < 655 then
                  (if o.val < 653 then
                    ![
                      0x402,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 654 then
                      ![
                        0x0,
                        0xff0000000000000000000000000000000000,
                        0x7f80000000000000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x2000000000000000000,
                        0x400000000000000000000
                      ]))
                else
                  (if o.val < 656 then
                    ![
                      0x0,
                      0x0,
                      0x3fdfe000000000,
                      0x0
                    ]
                  else
                    (if o.val < 657 then
                      ![
                        0x0,
                        0x3fc02000000000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x5fe000000000000000000000000000,
                        0x0
                      ])))
              else
                (if o.val < 661 then
                  (if o.val < 659 then
                    ![
                      0x0,
                      0xff0000000000000000,
                      0x7f80000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 660 then
                      ![
                        0x0,
                        0x0,
                        0x3fc00000000000000000000000000000,
                        0x2000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x5fe000000000000000000
                      ]))
                else
                  (if o.val < 662 then
                    (fun _ => 0)
                  else
                    (if o.val < 663 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))))))
      else
        (if o.val < 711 then
          (if o.val < 687 then
            (if o.val < 675 then
              (if o.val < 669 then
                (if o.val < 666 then
                  (if o.val < 665 then
                    (fun _ => 0)
                  else
                    (fun _ => 0))
                else
                  (if o.val < 667 then
                    (fun _ => 0)
                  else
                    (if o.val < 668 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 672 then
                  (if o.val < 670 then
                    (fun _ => 0)
                  else
                    (if o.val < 671 then
                      ![
                        0xff0080000000000000000000000000000000,
                        0x7f80000000000000000000000ff0000000,
                        0x10000000000000000000000000007f80000,
                        0xff0080000000000000000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x3fc02000000000
                      ]))
                else
                  (if o.val < 673 then
                    ![
                      0x0,
                      0x0,
                      0x5fe000000000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 674 then
                      ![
                        0x0,
                        0x10000000000000000,
                        0x80000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x10000000,
                        0x7f80000
                      ]))))
            else
              (if o.val < 681 then
                (if o.val < 678 then
                  (if o.val < 676 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x17f80000
                    ]
                  else
                    (if o.val < 677 then
                      ![
                        0x0,
                        0x0,
                        0x7f80000000000000,
                        0xff0000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x3fdfe000000000,
                        0x0
                      ]))
                else
                  (if o.val < 679 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x3fdfe000000000000000000000000000
                    ]
                  else
                    (if o.val < 680 then
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x10000000000000000000000000000000000,
                        0x80000000000000000000000000000000,
                        0x0
                      ])))
              else
                (if o.val < 684 then
                  (if o.val < 682 then
                    (fun _ => 0)
                  else
                    (if o.val < 683 then
                      (fun _ => 0)
                    else
                      ![
                        0xff0080000000000000000000000000000000,
                        0x7f80000000000000000000000ff0000000,
                        0x10000000000000000000000000007f80000,
                        0xff0080000000000000000000000000000000
                      ]))
                else
                  (if o.val < 685 then
                    (fun _ => 0)
                  else
                    (if o.val < 686 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))))
          else
            (if o.val < 699 then
              (if o.val < 693 then
                (if o.val < 690 then
                  (if o.val < 688 then
                    (fun _ => 0)
                  else
                    (if o.val < 689 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 691 then
                    (fun _ => 0)
                  else
                    (if o.val < 692 then
                      (fun _ => 0)
                    else
                      (fun _ => 0))))
              else
                (if o.val < 696 then
                  (if o.val < 694 then
                    ![
                      0x17f80000,
                      0xff0000000000000000000000000000080000,
                      0x7f80000000000000000000000ff0000000,
                      0x17f80000
                    ]
                  else
                    (if o.val < 695 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 697 then
                    (fun _ => 0)
                  else
                    (if o.val < 698 then
                      (fun _ => 0)
                    else
                      (fun _ => 0)))))
            else
              (if o.val < 705 then
                (if o.val < 702 then
                  (if o.val < 700 then
                    (fun _ => 0)
                  else
                    (if o.val < 701 then
                      (fun _ => 0)
                    else
                      ![
                        0x400,
                        0x1fe,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 703 then
                    ![
                      0x5fe000000000,
                      0x0,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 704 then
                      ![
                        0x3fc02000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x3fc02,
                        0x0,
                        0x0
                      ])))
              else
                (if o.val < 708 then
                  (if o.val < 706 then
                    ![
                      0x0,
                      0xff0000000000000000000000000,
                      0x7f80000000000000000000000,
                      0x0
                    ]
                  else
                    (if o.val < 707 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x402000000000000000000000000000
                      ]
                    else
                      ![
                        0x402,
                        0x0,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 709 then
                    ![
                      0x0,
                      0x10000000,
                      0x80000,
                      0x0
                    ]
                  else
                    (if o.val < 710 then
                      ![
                        0x2000000000,
                        0x400000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0xff7f80000,
                        0x0,
                        0x0
                      ]))))))
        else
          (if o.val < 735 then
            (if o.val < 723 then
              (if o.val < 717 then
                (if o.val < 714 then
                  (if o.val < 712 then
                    ![
                      0x0,
                      0x0,
                      0xff00801feff00005fe,
                      0x0
                    ]
                  else
                    (if o.val < 713 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x10080002ff003fdfe
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 715 then
                    ![
                      0x400007f80000000000000000000000,
                      0x0,
                      0x0,
                      0x17f8000201003fc02000000000000000000
                    ]
                  else
                    (if o.val < 716 then
                      (fun _ => 0)
                    else
                      ![
                        0xff00801feff00005fe000000000000000000,
                        0x0,
                        0x0,
                        0x400007f80000000000000000000000
                      ])))
              else
                (if o.val < 720 then
                  (if o.val < 718 then
                    ![
                      0x0,
                      0xff00801feff00005fe,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 719 then
                      ![
                        0x10080002ff003fdfe,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x17f8000201003fc02000000000000000000,
                        0x0,
                        0x0,
                        0x3fc00000080000000000000000000000
                      ]))
                else
                  (if o.val < 721 then
                    (fun _ => 0)
                  else
                    (if o.val < 722 then
                      ![
                        0xff7f801fe010000402,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x17f8000201003fc02,
                        0x0,
                        0x0
                      ]))))
            else
              (if o.val < 729 then
                (if o.val < 726 then
                  (if o.val < 724 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x10080002ff003fdfe
                    ]
                  else
                    (if o.val < 725 then
                      ![
                        0x0,
                        0x0,
                        0xff00801feff00005fe,
                        0x0
                      ]
                    else
                      ![
                        0x400007f80000000000000000000000,
                        0x0,
                        0x0,
                        0x17f8000201003fc02000000000000000000
                      ]))
                else
                  (if o.val < 727 then
                    (fun _ => 0)
                  else
                    (if o.val < 728 then
                      ![
                        0x0,
                        0x0,
                        0x400000080000000000000000000000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x3fc00007f80000,
                        0x0
                      ])))
              else
                (if o.val < 732 then
                  (if o.val < 730 then
                    ![
                      0xff0080002ff003fc02000000000000000000,
                      0x0,
                      0x0,
                      0x3fc00007f80000000000000000000000
                    ]
                  else
                    (if o.val < 731 then
                      (fun _ => 0)
                    else
                      ![
                        0x3fc00007f80000000000000000000000,
                        0x0,
                        0x0,
                        0x17f801fe0100005fe000000000000000000
                      ]))
                else
                  (if o.val < 733 then
                    (fun _ => 0)
                  else
                    (if o.val < 734 then
                      ![
                        0x0,
                        0x3fc00007f80000000000000000000000,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x400000080000,
                        0x0,
                        0x0
                      ])))))
          else
            (if o.val < 747 then
              (if o.val < 741 then
                (if o.val < 738 then
                  (if o.val < 736 then
                    (fun _ => 0)
                  else
                    (if o.val < 737 then
                      ![
                        0x3fc00007f80000000000000000000000,
                        0x0,
                        0x0,
                        0x17f801fe0100005fe000000000000000000
                      ]
                    else
                      ![
                        0x0,
                        0x400000080000,
                        0x0,
                        0x0
                      ]))
                else
                  (if o.val < 739 then
                    ![
                      0x0,
                      0x400000080000000000000000000000,
                      0x0,
                      0x0
                    ]
                  else
                    (if o.val < 740 then
                      ![
                        0x0,
                        0x0,
                        0x400000080000,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x400000080000000000000000000000,
                        0x0
                      ])))
              else
                (if o.val < 744 then
                  (if o.val < 742 then
                    (fun _ => 0)
                  else
                    (if o.val < 743 then
                      ![
                        0x17f801fe0100005fe000000000000000000,
                        0x0,
                        0x0,
                        0x400000080000000000000000000000
                      ]
                    else
                      ![
                        0x7f80000000000400000000000000000000,
                        0x0,
                        0x0,
                        0xff003fdfeff7f801fe000000000000000000
                      ]))
                else
                  (if o.val < 745 then
                    (fun _ => 0)
                  else
                    (if o.val < 746 then
                      ![
                        0x80000000000400,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x8000000003fc00000000000000000000
                      ]))))
            else
              (if o.val < 753 then
                (if o.val < 750 then
                  (if o.val < 748 then
                    ![
                      0x0,
                      0x0,
                      0x0,
                      0x80000000000400
                    ]
                  else
                    (if o.val < 749 then
                      ![
                        0x7f80000000000400000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0xff003fdfeff7f801fe000000000000000000,
                        0x0,
                        0x0,
                        0x8000000003fc00000000000000000000
                      ]))
                else
                  (if o.val < 751 then
                    (fun _ => 0)
                  else
                    (if o.val < 752 then
                      ![
                        0x7f80000000000400000000000000000000,
                        0x0,
                        0x0,
                        0x0
                      ]
                    else
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x7f8000000003fc00
                      ])))
              else
                (if o.val < 756 then
                  (if o.val < 754 then
                    (fun _ => 0)
                  else
                    (if o.val < 755 then
                      ![
                        0x10000402010080002000000000000000000,
                        0x0,
                        0x0,
                        0x7f80000000000400000000000000000000
                      ]
                    else
                      (fun _ => 0)))
                else
                  (if o.val < 757 then
                    ![
                      0x7f80000000000400000000000000000000,
                      0x0,
                      0x0,
                      0xff003fdfeff7f801fe000000000000000000
                    ]
                  else
                    (if o.val < 758 then
                      ![
                        0x0,
                        0x0,
                        0x0,
                        0x7f80000000000400000000000000000000
                      ]
                    else
                      ![
                        0x80000000000400,
                        0x0,
                        0x0,
                        0x0
                      ]))))))))))

/-- Decode the complete original signed coefficient, including every zero. -/
def generatedTwelfthIncomingOctadCache (o : Fin 759) (e : Fin 64) : ℤ :=
  let v := (generatedTwelfthIncomingOctadCacheWords o ⟨e.val / 16, by omega⟩ /
    2 ^ (9 * (e.val % 16))) % 512
  if v < 256 then (v : ℤ) else (v : ℤ) - 512

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
