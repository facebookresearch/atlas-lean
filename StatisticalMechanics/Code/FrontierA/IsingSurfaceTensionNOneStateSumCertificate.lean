/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







import Code.FrontierA.IsingSurfaceTensionNOneBlocksGenerated
import Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics
import Code.FrontierA.NOneStateSumBlocks.Block00
import Code.FrontierA.NOneStateSumBlocks.Block01
import Code.FrontierA.NOneStateSumBlocks.Block02
import Code.FrontierA.NOneStateSumBlocks.Block03
import Code.FrontierA.NOneStateSumBlocks.Block04
import Code.FrontierA.NOneStateSumBlocks.Block05
import Code.FrontierA.NOneStateSumBlocks.Block06
import Code.FrontierA.NOneStateSumBlocks.Block07
import Code.FrontierA.NOneStateSumBlocks.Block08
import Code.FrontierA.NOneStateSumBlocks.Block09
import Code.FrontierA.NOneStateSumBlocks.Block10
import Code.FrontierA.NOneStateSumBlocks.Block11
import Code.FrontierA.NOneStateSumBlocks.Block12
import Code.FrontierA.NOneStateSumBlocks.Block13
import Code.FrontierA.NOneStateSumBlocks.Block14
import Code.FrontierA.NOneStateSumBlocks.Block15
import Code.FrontierA.NOneStateSumBlocks.Block16
import Code.FrontierA.NOneStateSumBlocks.Block17
import Code.FrontierA.NOneStateSumBlocks.Block18
import Code.FrontierA.NOneStateSumBlocks.Block19
import Code.FrontierA.NOneStateSumBlocks.Block20
import Code.FrontierA.NOneStateSumBlocks.Block21
import Code.FrontierA.NOneStateSumBlocks.Block22
import Code.FrontierA.NOneStateSumBlocks.Block23
import Code.FrontierA.NOneStateSumBlocks.Block24
import Code.FrontierA.NOneStateSumBlocks.Block25
import Code.FrontierA.NOneStateSumBlocks.Block26
import Code.FrontierA.NOneStateSumBlocks.Block27
import Code.FrontierA.NOneStateSumBlocks.Block28
import Code.FrontierA.NOneStateSumBlocks.Block29
import Code.FrontierA.NOneStateSumBlocks.Block30
import Code.FrontierA.NOneStateSumBlocks.Block31
import Code.FrontierA.NOneStateSumBlocks.Block32
import Code.FrontierA.NOneStateSumBlocks.Block33
import Code.FrontierA.NOneStateSumBlocks.Block34
import Code.FrontierA.NOneStateSumBlocks.Block35
import Code.FrontierA.NOneStateSumBlocks.Block36
import Code.FrontierA.NOneStateSumBlocks.Block37
import Code.FrontierA.NOneStateSumBlocks.Block38
import Code.FrontierA.NOneStateSumBlocks.Block39
import Code.FrontierA.NOneStateSumBlocks.Block40
import Code.FrontierA.NOneStateSumBlocks.Block41
import Code.FrontierA.NOneStateSumBlocks.Block42
import Code.FrontierA.NOneStateSumBlocks.Block43
import Code.FrontierA.NOneStateSumBlocks.Block44
import Code.FrontierA.NOneStateSumBlocks.Block45
import Code.FrontierA.NOneStateSumBlocks.Block46
import Code.FrontierA.NOneStateSumBlocks.Block47
import Code.FrontierA.NOneStateSumBlocks.Block48
import Code.FrontierA.NOneStateSumBlocks.Block49
import Code.FrontierA.NOneStateSumBlocks.Block50
import Code.FrontierA.NOneStateSumBlocks.Block51
import Code.FrontierA.NOneStateSumBlocks.Block52
import Code.FrontierA.NOneStateSumBlocks.Block53
import Code.FrontierA.NOneStateSumBlocks.Block54
import Code.FrontierA.NOneStateSumBlocks.Block55
import Code.FrontierA.NOneStateSumBlocks.Block56
import Code.FrontierA.NOneStateSumBlocks.Block57
import Code.FrontierA.NOneStateSumBlocks.Block58
import Code.FrontierA.NOneStateSumBlocks.Block59
import Code.FrontierA.NOneStateSumBlocks.Block60
import Code.FrontierA.NOneStateSumBlocks.Block61
import Code.FrontierA.NOneStateSumBlocks.Block62
import Code.FrontierA.NOneStateSumBlocks.Block63
import Code.FrontierA.NOneStateSumBlocks.Block64
import Code.FrontierA.NOneStateSumBlocks.Block65
import Code.FrontierA.NOneStateSumBlocks.Block66
import Code.FrontierA.NOneStateSumBlocks.Block67
import Code.FrontierA.NOneStateSumBlocks.Block68
import Code.FrontierA.NOneStateSumBlocks.Block69
import Code.FrontierA.NOneStateSumBlocks.Block70
import Code.FrontierA.NOneStateSumBlocks.Block71
import Code.FrontierA.NOneStateSumBlocks.Block72
import Code.FrontierA.NOneStateSumBlocks.Block73
import Code.FrontierA.NOneStateSumBlocks.Block74
import Code.FrontierA.NOneStateSumBlocks.Block75
import Code.FrontierA.NOneStateSumBlocks.Block76
import Code.FrontierA.NOneStateSumBlocks.Block77
import Code.FrontierA.NOneStateSumBlocks.Block78
import Code.FrontierA.NOneStateSumBlocks.Block79
import Code.FrontierA.NOneStateSumBlocks.Block80
import Code.FrontierA.NOneStateSumBlocks.Block81
import Code.FrontierA.NOneStateSumBlocks.Block82
import Code.FrontierA.NOneStateSumBlocks.Block83
import Code.FrontierA.NOneStateSumBlocks.Block84
import Code.FrontierA.NOneStateSumBlocks.Block85
import Code.FrontierA.NOneStateSumBlocks.Block86
import Code.FrontierA.NOneStateSumBlocks.Block87
import Code.FrontierA.NOneStateSumBlocks.Block88
import Code.FrontierA.NOneStateSumBlocks.Block89
import Code.FrontierA.NOneStateSumBlocks.Block90
import Code.FrontierA.NOneStateSumBlocks.Block91
import Code.FrontierA.NOneStateSumBlocks.Block92
import Code.FrontierA.NOneStateSumBlocks.Block93
import Code.FrontierA.NOneStateSumBlocks.Block94
import Code.FrontierA.NOneStateSumBlocks.Block95
import Code.FrontierA.NOneStateSumBlocks.Block96
import Code.FrontierA.NOneStateSumBlocks.Block97
import Code.FrontierA.NOneStateSumBlocks.Block98
import Code.FrontierA.NOneStateSumBlocks.Block99
import Code.FrontierA.NOneStateSumBlocks.Block100
import Code.FrontierA.NOneStateSumBlocks.Block101
import Code.FrontierA.NOneStateSumBlocks.Block102
import Code.FrontierA.NOneStateSumBlocks.Block103
import Code.FrontierA.NOneStateSumBlocks.Block104
import Code.FrontierA.NOneStateSumBlocks.Block105
import Code.FrontierA.NOneStateSumBlocks.Block106
import Code.FrontierA.NOneStateSumBlocks.Block107
import Code.FrontierA.NOneStateSumBlocks.Block108
import Code.FrontierA.NOneStateSumBlocks.Block109
import Code.FrontierA.NOneStateSumBlocks.Block110
import Code.FrontierA.NOneStateSumBlocks.Block111
import Code.FrontierA.NOneStateSumBlocks.Block112
import Code.FrontierA.NOneStateSumBlocks.Block113
import Code.FrontierA.NOneStateSumBlocks.Block114
import Code.FrontierA.NOneStateSumBlocks.Block115
import Code.FrontierA.NOneStateSumBlocks.Block116
import Code.FrontierA.NOneStateSumBlocks.Block117
import Code.FrontierA.NOneStateSumBlocks.Block118
import Code.FrontierA.NOneStateSumBlocks.Block119
import Code.FrontierA.NOneStateSumBlocks.Block120
import Code.FrontierA.NOneStateSumBlocks.Block121
import Code.FrontierA.NOneStateSumBlocks.Block122
import Code.FrontierA.NOneStateSumBlocks.Block123
import Code.FrontierA.NOneStateSumBlocks.Block124
import Code.FrontierA.NOneStateSumBlocks.Block125
import Code.FrontierA.NOneStateSumBlocks.Block126
import Code.FrontierA.NOneStateSumBlocks.Block127
import Code.FrontierA.NOneStateSumBlocks.Block128
import Code.FrontierA.NOneStateSumBlocks.Block129
import Code.FrontierA.NOneStateSumBlocks.Block130
import Code.FrontierA.NOneStateSumBlocks.Block131
import Code.FrontierA.NOneStateSumBlocks.Block132
import Code.FrontierA.NOneStateSumBlocks.Block133
import Code.FrontierA.NOneStateSumBlocks.Block134
import Code.FrontierA.NOneStateSumBlocks.Block135
import Code.FrontierA.NOneStateSumBlocks.Block136
import Code.FrontierA.NOneStateSumBlocks.Block137
import Code.FrontierA.NOneStateSumBlocks.Block138
import Code.FrontierA.NOneStateSumBlocks.Block139
import Code.FrontierA.NOneStateSumBlocks.Block140
import Code.FrontierA.NOneStateSumBlocks.Block141
import Code.FrontierA.NOneStateSumBlocks.Block142
import Code.FrontierA.NOneStateSumBlocks.Block143
import Code.FrontierA.NOneStateSumBlocks.Block144
import Code.FrontierA.NOneStateSumBlocks.Block145
import Code.FrontierA.NOneStateSumBlocks.Block146
import Code.FrontierA.NOneStateSumBlocks.Block147
import Code.FrontierA.NOneStateSumBlocks.Block148
import Code.FrontierA.NOneStateSumBlocks.Block149
import Code.FrontierA.NOneStateSumBlocks.Block150
import Code.FrontierA.NOneStateSumBlocks.Block151
import Code.FrontierA.NOneStateSumBlocks.Block152
import Code.FrontierA.NOneStateSumBlocks.Block153
import Code.FrontierA.NOneStateSumBlocks.Block154
import Code.FrontierA.NOneStateSumBlocks.Block155
import Code.FrontierA.NOneStateSumBlocks.Block156
import Code.FrontierA.NOneStateSumBlocks.Block157
import Code.FrontierA.NOneStateSumBlocks.Block158
import Code.FrontierA.NOneStateSumBlocks.Block159
import Code.FrontierA.NOneStateSumBlocks.Block160
import Code.FrontierA.NOneStateSumBlocks.Block161
import Code.FrontierA.NOneStateSumBlocks.Block162
import Code.FrontierA.NOneStateSumBlocks.Block163
import Code.FrontierA.NOneStateSumBlocks.Block164
import Code.FrontierA.NOneStateSumBlocks.Block165
import Code.FrontierA.NOneStateSumBlocks.Block166
import Code.FrontierA.NOneStateSumBlocks.Block167
import Code.FrontierA.NOneStateSumBlocks.Block168
import Code.FrontierA.NOneStateSumBlocks.Block169
import Code.FrontierA.NOneStateSumBlocks.Block170
import Code.FrontierA.NOneStateSumBlocks.Block171
import Code.FrontierA.NOneStateSumBlocks.Block172
import Code.FrontierA.NOneStateSumBlocks.Block173
import Code.FrontierA.NOneStateSumBlocks.Block174
import Code.FrontierA.NOneStateSumBlocks.Block175
import Code.FrontierA.NOneStateSumBlocks.Block176
import Code.FrontierA.NOneStateSumBlocks.Block177
import Code.FrontierA.NOneStateSumBlocks.Block178
import Code.FrontierA.NOneStateSumBlocks.Block179
import Code.FrontierA.NOneStateSumBlocks.Block180
import Code.FrontierA.NOneStateSumBlocks.Block181
import Code.FrontierA.NOneStateSumBlocks.Block182
import Code.FrontierA.NOneStateSumBlocks.Block183
import Code.FrontierA.NOneStateSumBlocks.Block184
import Code.FrontierA.NOneStateSumBlocks.Block185
import Code.FrontierA.NOneStateSumBlocks.Block186
import Code.FrontierA.NOneStateSumBlocks.Block187
import Code.FrontierA.NOneStateSumBlocks.Block188
import Code.FrontierA.NOneStateSumBlocks.Block189
import Code.FrontierA.NOneStateSumBlocks.Block190
import Code.FrontierA.NOneStateSumBlocks.Block191
import Code.FrontierA.NOneStateSumBlocks.Block192
import Code.FrontierA.NOneStateSumBlocks.Block193
import Code.FrontierA.NOneStateSumBlocks.Block194
import Code.FrontierA.NOneStateSumBlocks.Block195
import Code.FrontierA.NOneStateSumBlocks.Block196
import Code.FrontierA.NOneStateSumBlocks.Block197
import Code.FrontierA.NOneStateSumBlocks.Block198
import Code.FrontierA.NOneStateSumBlocks.Block199
import Code.FrontierA.NOneStateSumBlocks.Block200
import Code.FrontierA.NOneStateSumBlocks.Block201
import Code.FrontierA.NOneStateSumBlocks.Block202
import Code.FrontierA.NOneStateSumBlocks.Block203
import Code.FrontierA.NOneStateSumBlocks.Block204
import Code.FrontierA.NOneStateSumBlocks.Block205
import Code.FrontierA.NOneStateSumBlocks.Block206
import Code.FrontierA.NOneStateSumBlocks.Block207
import Code.FrontierA.NOneStateSumBlocks.Block208
import Code.FrontierA.NOneStateSumBlocks.Block209
import Code.FrontierA.NOneStateSumBlocks.Block210
import Code.FrontierA.NOneStateSumBlocks.Block211
import Code.FrontierA.NOneStateSumBlocks.Block212
import Code.FrontierA.NOneStateSumBlocks.Block213
import Code.FrontierA.NOneStateSumBlocks.Block214
import Code.FrontierA.NOneStateSumBlocks.Block215
import Code.FrontierA.NOneStateSumBlocks.Block216
import Code.FrontierA.NOneStateSumBlocks.Block217
import Code.FrontierA.NOneStateSumBlocks.Block218
import Code.FrontierA.NOneStateSumBlocks.Block219
import Code.FrontierA.NOneStateSumBlocks.Block220
import Code.FrontierA.NOneStateSumBlocks.Block221
import Code.FrontierA.NOneStateSumBlocks.Block222
import Code.FrontierA.NOneStateSumBlocks.Block223
import Code.FrontierA.NOneStateSumBlocks.Block224
import Code.FrontierA.NOneStateSumBlocks.Block225
import Code.FrontierA.NOneStateSumBlocks.Block226
import Code.FrontierA.NOneStateSumBlocks.Block227
import Code.FrontierA.NOneStateSumBlocks.Block228
import Code.FrontierA.NOneStateSumBlocks.Block229
import Code.FrontierA.NOneStateSumBlocks.Block230
import Code.FrontierA.NOneStateSumBlocks.Block231
import Code.FrontierA.NOneStateSumBlocks.Block232
import Code.FrontierA.NOneStateSumBlocks.Block233
import Code.FrontierA.NOneStateSumBlocks.Block234
import Code.FrontierA.NOneStateSumBlocks.Block235
import Code.FrontierA.NOneStateSumBlocks.Block236
import Code.FrontierA.NOneStateSumBlocks.Block237
import Code.FrontierA.NOneStateSumBlocks.Block238
import Code.FrontierA.NOneStateSumBlocks.Block239
import Code.FrontierA.NOneStateSumBlocks.Block240
import Code.FrontierA.NOneStateSumBlocks.Block241
import Code.FrontierA.NOneStateSumBlocks.Block242
import Code.FrontierA.NOneStateSumBlocks.Block243
import Code.FrontierA.NOneStateSumBlocks.Block244
import Code.FrontierA.NOneStateSumBlocks.Block245
import Code.FrontierA.NOneStateSumBlocks.Block246
import Code.FrontierA.NOneStateSumBlocks.Block247
import Code.FrontierA.NOneStateSumBlocks.Block248
import Code.FrontierA.NOneStateSumBlocks.Block249
import Code.FrontierA.NOneStateSumBlocks.Block250
import Code.FrontierA.NOneStateSumBlocks.Block251
import Code.FrontierA.NOneStateSumBlocks.Block252
import Code.FrontierA.NOneStateSumBlocks.Block253
import Code.FrontierA.NOneStateSumBlocks.Block254
import Code.FrontierA.NOneStateSumBlocks.Block255








namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def generatedDirectStateSum : BiPoly :=
  BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.monomial 0 0 0)
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock0))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock1))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock2))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock3))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock4))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock5))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock6))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock7))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock8))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock9))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock10))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock11))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock12))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock13))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock14))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock15))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock16))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock17))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock18))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock19))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock20))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock21))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock22))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock23))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock24))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock25))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock26))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock27))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock28))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock29))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock30))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock31))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock32))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock33))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock34))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock35))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock36))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock37))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock38))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock39))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock40))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock41))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock42))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock43))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock44))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock45))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock46))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock47))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock48))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock49))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock50))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock51))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock52))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock53))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock54))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock55))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock56))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock57))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock58))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock59))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock60))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock61))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock62))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock63))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock64))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock65))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock66))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock67))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock68))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock69))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock70))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock71))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock72))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock73))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock74))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock75))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock76))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock77))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock78))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock79))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock80))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock81))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock82))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock83))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock84))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock85))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock86))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock87))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock88))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock89))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock90))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock91))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock92))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock93))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock94))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock95))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock96))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock97))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock98))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock99))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock100))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock101))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock102))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock103))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock104))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock105))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock106))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock107))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock108))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock109))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock110))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock111))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock112))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock113))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock114))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock115))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock116))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock117))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock118))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock119))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock120))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock121))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock122))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock123))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock124))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock125))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock126))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock127))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock128))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock129))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock130))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock131))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock132))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock133))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock134))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock135))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock136))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock137))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock138))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock139))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock140))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock141))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock142))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock143))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock144))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock145))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock146))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock147))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock148))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock149))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock150))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock151))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock152))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock153))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock154))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock155))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock156))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock157))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock158))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock159))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock160))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock161))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock162))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock163))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock164))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock165))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock166))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock167))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock168))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock169))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock170))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock171))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock172))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock173))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock174))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock175))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock176))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock177))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock178))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock179))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock180))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock181))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock182))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock183))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock184))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock185))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock186))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock187))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock188))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock189))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock190))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock191))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock192))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock193))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock194))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock195))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock196))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock197))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock198))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock199))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock200))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock201))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock202))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock203))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock204))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock205))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock206))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock207))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock208))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock209))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock210))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock211))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock212))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock213))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock214))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock215))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock216))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock217))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock218))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock219))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock220))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock221))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock222))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock223))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock224))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock225))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock226))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock227))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock228))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock229))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock230))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock231))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock232))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock233))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock234))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock235))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock236))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock237))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock238))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock239))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock240))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock241))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock242))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock243))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock244))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock245))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock246))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock247))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock248))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock249))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock250))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock251))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock252))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock253))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock254))
    (rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock255)

set_option maxRecDepth 1000000 in
theorem rawMomentPolyStateSum_eq_generatedDirectStateSum :
    rawMomentPolyStateSum = generatedDirectStateSum := by
  unfold rawMomentPolyStateSum
  change BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.add (BiPoly.monomial 0 0 0)
    (rawMomentDirectBlock 0 2))
    (rawMomentDirectBlock 2 2))
    (rawMomentDirectBlock 4 2))
    (rawMomentDirectBlock 6 2))
    (rawMomentDirectBlock 8 2))
    (rawMomentDirectBlock 10 2))
    (rawMomentDirectBlock 12 2))
    (rawMomentDirectBlock 14 2))
    (rawMomentDirectBlock 16 2))
    (rawMomentDirectBlock 18 2))
    (rawMomentDirectBlock 20 2))
    (rawMomentDirectBlock 22 2))
    (rawMomentDirectBlock 24 2))
    (rawMomentDirectBlock 26 2))
    (rawMomentDirectBlock 28 2))
    (rawMomentDirectBlock 30 2))
    (rawMomentDirectBlock 32 2))
    (rawMomentDirectBlock 34 2))
    (rawMomentDirectBlock 36 2))
    (rawMomentDirectBlock 38 2))
    (rawMomentDirectBlock 40 2))
    (rawMomentDirectBlock 42 2))
    (rawMomentDirectBlock 44 2))
    (rawMomentDirectBlock 46 2))
    (rawMomentDirectBlock 48 2))
    (rawMomentDirectBlock 50 2))
    (rawMomentDirectBlock 52 2))
    (rawMomentDirectBlock 54 2))
    (rawMomentDirectBlock 56 2))
    (rawMomentDirectBlock 58 2))
    (rawMomentDirectBlock 60 2))
    (rawMomentDirectBlock 62 2))
    (rawMomentDirectBlock 64 2))
    (rawMomentDirectBlock 66 2))
    (rawMomentDirectBlock 68 2))
    (rawMomentDirectBlock 70 2))
    (rawMomentDirectBlock 72 2))
    (rawMomentDirectBlock 74 2))
    (rawMomentDirectBlock 76 2))
    (rawMomentDirectBlock 78 2))
    (rawMomentDirectBlock 80 2))
    (rawMomentDirectBlock 82 2))
    (rawMomentDirectBlock 84 2))
    (rawMomentDirectBlock 86 2))
    (rawMomentDirectBlock 88 2))
    (rawMomentDirectBlock 90 2))
    (rawMomentDirectBlock 92 2))
    (rawMomentDirectBlock 94 2))
    (rawMomentDirectBlock 96 2))
    (rawMomentDirectBlock 98 2))
    (rawMomentDirectBlock 100 2))
    (rawMomentDirectBlock 102 2))
    (rawMomentDirectBlock 104 2))
    (rawMomentDirectBlock 106 2))
    (rawMomentDirectBlock 108 2))
    (rawMomentDirectBlock 110 2))
    (rawMomentDirectBlock 112 2))
    (rawMomentDirectBlock 114 2))
    (rawMomentDirectBlock 116 2))
    (rawMomentDirectBlock 118 2))
    (rawMomentDirectBlock 120 2))
    (rawMomentDirectBlock 122 2))
    (rawMomentDirectBlock 124 2))
    (rawMomentDirectBlock 126 2))
    (rawMomentDirectBlock 128 2))
    (rawMomentDirectBlock 130 2))
    (rawMomentDirectBlock 132 2))
    (rawMomentDirectBlock 134 2))
    (rawMomentDirectBlock 136 2))
    (rawMomentDirectBlock 138 2))
    (rawMomentDirectBlock 140 2))
    (rawMomentDirectBlock 142 2))
    (rawMomentDirectBlock 144 2))
    (rawMomentDirectBlock 146 2))
    (rawMomentDirectBlock 148 2))
    (rawMomentDirectBlock 150 2))
    (rawMomentDirectBlock 152 2))
    (rawMomentDirectBlock 154 2))
    (rawMomentDirectBlock 156 2))
    (rawMomentDirectBlock 158 2))
    (rawMomentDirectBlock 160 2))
    (rawMomentDirectBlock 162 2))
    (rawMomentDirectBlock 164 2))
    (rawMomentDirectBlock 166 2))
    (rawMomentDirectBlock 168 2))
    (rawMomentDirectBlock 170 2))
    (rawMomentDirectBlock 172 2))
    (rawMomentDirectBlock 174 2))
    (rawMomentDirectBlock 176 2))
    (rawMomentDirectBlock 178 2))
    (rawMomentDirectBlock 180 2))
    (rawMomentDirectBlock 182 2))
    (rawMomentDirectBlock 184 2))
    (rawMomentDirectBlock 186 2))
    (rawMomentDirectBlock 188 2))
    (rawMomentDirectBlock 190 2))
    (rawMomentDirectBlock 192 2))
    (rawMomentDirectBlock 194 2))
    (rawMomentDirectBlock 196 2))
    (rawMomentDirectBlock 198 2))
    (rawMomentDirectBlock 200 2))
    (rawMomentDirectBlock 202 2))
    (rawMomentDirectBlock 204 2))
    (rawMomentDirectBlock 206 2))
    (rawMomentDirectBlock 208 2))
    (rawMomentDirectBlock 210 2))
    (rawMomentDirectBlock 212 2))
    (rawMomentDirectBlock 214 2))
    (rawMomentDirectBlock 216 2))
    (rawMomentDirectBlock 218 2))
    (rawMomentDirectBlock 220 2))
    (rawMomentDirectBlock 222 2))
    (rawMomentDirectBlock 224 2))
    (rawMomentDirectBlock 226 2))
    (rawMomentDirectBlock 228 2))
    (rawMomentDirectBlock 230 2))
    (rawMomentDirectBlock 232 2))
    (rawMomentDirectBlock 234 2))
    (rawMomentDirectBlock 236 2))
    (rawMomentDirectBlock 238 2))
    (rawMomentDirectBlock 240 2))
    (rawMomentDirectBlock 242 2))
    (rawMomentDirectBlock 244 2))
    (rawMomentDirectBlock 246 2))
    (rawMomentDirectBlock 248 2))
    (rawMomentDirectBlock 250 2))
    (rawMomentDirectBlock 252 2))
    (rawMomentDirectBlock 254 2))
    (rawMomentDirectBlock 256 2))
    (rawMomentDirectBlock 258 2))
    (rawMomentDirectBlock 260 2))
    (rawMomentDirectBlock 262 2))
    (rawMomentDirectBlock 264 2))
    (rawMomentDirectBlock 266 2))
    (rawMomentDirectBlock 268 2))
    (rawMomentDirectBlock 270 2))
    (rawMomentDirectBlock 272 2))
    (rawMomentDirectBlock 274 2))
    (rawMomentDirectBlock 276 2))
    (rawMomentDirectBlock 278 2))
    (rawMomentDirectBlock 280 2))
    (rawMomentDirectBlock 282 2))
    (rawMomentDirectBlock 284 2))
    (rawMomentDirectBlock 286 2))
    (rawMomentDirectBlock 288 2))
    (rawMomentDirectBlock 290 2))
    (rawMomentDirectBlock 292 2))
    (rawMomentDirectBlock 294 2))
    (rawMomentDirectBlock 296 2))
    (rawMomentDirectBlock 298 2))
    (rawMomentDirectBlock 300 2))
    (rawMomentDirectBlock 302 2))
    (rawMomentDirectBlock 304 2))
    (rawMomentDirectBlock 306 2))
    (rawMomentDirectBlock 308 2))
    (rawMomentDirectBlock 310 2))
    (rawMomentDirectBlock 312 2))
    (rawMomentDirectBlock 314 2))
    (rawMomentDirectBlock 316 2))
    (rawMomentDirectBlock 318 2))
    (rawMomentDirectBlock 320 2))
    (rawMomentDirectBlock 322 2))
    (rawMomentDirectBlock 324 2))
    (rawMomentDirectBlock 326 2))
    (rawMomentDirectBlock 328 2))
    (rawMomentDirectBlock 330 2))
    (rawMomentDirectBlock 332 2))
    (rawMomentDirectBlock 334 2))
    (rawMomentDirectBlock 336 2))
    (rawMomentDirectBlock 338 2))
    (rawMomentDirectBlock 340 2))
    (rawMomentDirectBlock 342 2))
    (rawMomentDirectBlock 344 2))
    (rawMomentDirectBlock 346 2))
    (rawMomentDirectBlock 348 2))
    (rawMomentDirectBlock 350 2))
    (rawMomentDirectBlock 352 2))
    (rawMomentDirectBlock 354 2))
    (rawMomentDirectBlock 356 2))
    (rawMomentDirectBlock 358 2))
    (rawMomentDirectBlock 360 2))
    (rawMomentDirectBlock 362 2))
    (rawMomentDirectBlock 364 2))
    (rawMomentDirectBlock 366 2))
    (rawMomentDirectBlock 368 2))
    (rawMomentDirectBlock 370 2))
    (rawMomentDirectBlock 372 2))
    (rawMomentDirectBlock 374 2))
    (rawMomentDirectBlock 376 2))
    (rawMomentDirectBlock 378 2))
    (rawMomentDirectBlock 380 2))
    (rawMomentDirectBlock 382 2))
    (rawMomentDirectBlock 384 2))
    (rawMomentDirectBlock 386 2))
    (rawMomentDirectBlock 388 2))
    (rawMomentDirectBlock 390 2))
    (rawMomentDirectBlock 392 2))
    (rawMomentDirectBlock 394 2))
    (rawMomentDirectBlock 396 2))
    (rawMomentDirectBlock 398 2))
    (rawMomentDirectBlock 400 2))
    (rawMomentDirectBlock 402 2))
    (rawMomentDirectBlock 404 2))
    (rawMomentDirectBlock 406 2))
    (rawMomentDirectBlock 408 2))
    (rawMomentDirectBlock 410 2))
    (rawMomentDirectBlock 412 2))
    (rawMomentDirectBlock 414 2))
    (rawMomentDirectBlock 416 2))
    (rawMomentDirectBlock 418 2))
    (rawMomentDirectBlock 420 2))
    (rawMomentDirectBlock 422 2))
    (rawMomentDirectBlock 424 2))
    (rawMomentDirectBlock 426 2))
    (rawMomentDirectBlock 428 2))
    (rawMomentDirectBlock 430 2))
    (rawMomentDirectBlock 432 2))
    (rawMomentDirectBlock 434 2))
    (rawMomentDirectBlock 436 2))
    (rawMomentDirectBlock 438 2))
    (rawMomentDirectBlock 440 2))
    (rawMomentDirectBlock 442 2))
    (rawMomentDirectBlock 444 2))
    (rawMomentDirectBlock 446 2))
    (rawMomentDirectBlock 448 2))
    (rawMomentDirectBlock 450 2))
    (rawMomentDirectBlock 452 2))
    (rawMomentDirectBlock 454 2))
    (rawMomentDirectBlock 456 2))
    (rawMomentDirectBlock 458 2))
    (rawMomentDirectBlock 460 2))
    (rawMomentDirectBlock 462 2))
    (rawMomentDirectBlock 464 2))
    (rawMomentDirectBlock 466 2))
    (rawMomentDirectBlock 468 2))
    (rawMomentDirectBlock 470 2))
    (rawMomentDirectBlock 472 2))
    (rawMomentDirectBlock 474 2))
    (rawMomentDirectBlock 476 2))
    (rawMomentDirectBlock 478 2))
    (rawMomentDirectBlock 480 2))
    (rawMomentDirectBlock 482 2))
    (rawMomentDirectBlock 484 2))
    (rawMomentDirectBlock 486 2))
    (rawMomentDirectBlock 488 2))
    (rawMomentDirectBlock 490 2))
    (rawMomentDirectBlock 492 2))
    (rawMomentDirectBlock 494 2))
    (rawMomentDirectBlock 496 2))
    (rawMomentDirectBlock 498 2))
    (rawMomentDirectBlock 500 2))
    (rawMomentDirectBlock 502 2))
    (rawMomentDirectBlock 504 2))
    (rawMomentDirectBlock 506 2))
    (rawMomentDirectBlock 508 2))
    (rawMomentDirectBlock 510 2) = generatedDirectStateSum
  rw [directStateBlock0_checked]
  rw [directStateBlock1_checked]
  rw [directStateBlock2_checked]
  rw [directStateBlock3_checked]
  rw [directStateBlock4_checked]
  rw [directStateBlock5_checked]
  rw [directStateBlock6_checked]
  rw [directStateBlock7_checked]
  rw [directStateBlock8_checked]
  rw [directStateBlock9_checked]
  rw [directStateBlock10_checked]
  rw [directStateBlock11_checked]
  rw [directStateBlock12_checked]
  rw [directStateBlock13_checked]
  rw [directStateBlock14_checked]
  rw [directStateBlock15_checked]
  rw [directStateBlock16_checked]
  rw [directStateBlock17_checked]
  rw [directStateBlock18_checked]
  rw [directStateBlock19_checked]
  rw [directStateBlock20_checked]
  rw [directStateBlock21_checked]
  rw [directStateBlock22_checked]
  rw [directStateBlock23_checked]
  rw [directStateBlock24_checked]
  rw [directStateBlock25_checked]
  rw [directStateBlock26_checked]
  rw [directStateBlock27_checked]
  rw [directStateBlock28_checked]
  rw [directStateBlock29_checked]
  rw [directStateBlock30_checked]
  rw [directStateBlock31_checked]
  rw [directStateBlock32_checked]
  rw [directStateBlock33_checked]
  rw [directStateBlock34_checked]
  rw [directStateBlock35_checked]
  rw [directStateBlock36_checked]
  rw [directStateBlock37_checked]
  rw [directStateBlock38_checked]
  rw [directStateBlock39_checked]
  rw [directStateBlock40_checked]
  rw [directStateBlock41_checked]
  rw [directStateBlock42_checked]
  rw [directStateBlock43_checked]
  rw [directStateBlock44_checked]
  rw [directStateBlock45_checked]
  rw [directStateBlock46_checked]
  rw [directStateBlock47_checked]
  rw [directStateBlock48_checked]
  rw [directStateBlock49_checked]
  rw [directStateBlock50_checked]
  rw [directStateBlock51_checked]
  rw [directStateBlock52_checked]
  rw [directStateBlock53_checked]
  rw [directStateBlock54_checked]
  rw [directStateBlock55_checked]
  rw [directStateBlock56_checked]
  rw [directStateBlock57_checked]
  rw [directStateBlock58_checked]
  rw [directStateBlock59_checked]
  rw [directStateBlock60_checked]
  rw [directStateBlock61_checked]
  rw [directStateBlock62_checked]
  rw [directStateBlock63_checked]
  rw [directStateBlock64_checked]
  rw [directStateBlock65_checked]
  rw [directStateBlock66_checked]
  rw [directStateBlock67_checked]
  rw [directStateBlock68_checked]
  rw [directStateBlock69_checked]
  rw [directStateBlock70_checked]
  rw [directStateBlock71_checked]
  rw [directStateBlock72_checked]
  rw [directStateBlock73_checked]
  rw [directStateBlock74_checked]
  rw [directStateBlock75_checked]
  rw [directStateBlock76_checked]
  rw [directStateBlock77_checked]
  rw [directStateBlock78_checked]
  rw [directStateBlock79_checked]
  rw [directStateBlock80_checked]
  rw [directStateBlock81_checked]
  rw [directStateBlock82_checked]
  rw [directStateBlock83_checked]
  rw [directStateBlock84_checked]
  rw [directStateBlock85_checked]
  rw [directStateBlock86_checked]
  rw [directStateBlock87_checked]
  rw [directStateBlock88_checked]
  rw [directStateBlock89_checked]
  rw [directStateBlock90_checked]
  rw [directStateBlock91_checked]
  rw [directStateBlock92_checked]
  rw [directStateBlock93_checked]
  rw [directStateBlock94_checked]
  rw [directStateBlock95_checked]
  rw [directStateBlock96_checked]
  rw [directStateBlock97_checked]
  rw [directStateBlock98_checked]
  rw [directStateBlock99_checked]
  rw [directStateBlock100_checked]
  rw [directStateBlock101_checked]
  rw [directStateBlock102_checked]
  rw [directStateBlock103_checked]
  rw [directStateBlock104_checked]
  rw [directStateBlock105_checked]
  rw [directStateBlock106_checked]
  rw [directStateBlock107_checked]
  rw [directStateBlock108_checked]
  rw [directStateBlock109_checked]
  rw [directStateBlock110_checked]
  rw [directStateBlock111_checked]
  rw [directStateBlock112_checked]
  rw [directStateBlock113_checked]
  rw [directStateBlock114_checked]
  rw [directStateBlock115_checked]
  rw [directStateBlock116_checked]
  rw [directStateBlock117_checked]
  rw [directStateBlock118_checked]
  rw [directStateBlock119_checked]
  rw [directStateBlock120_checked]
  rw [directStateBlock121_checked]
  rw [directStateBlock122_checked]
  rw [directStateBlock123_checked]
  rw [directStateBlock124_checked]
  rw [directStateBlock125_checked]
  rw [directStateBlock126_checked]
  rw [directStateBlock127_checked]
  rw [directStateBlock128_checked]
  rw [directStateBlock129_checked]
  rw [directStateBlock130_checked]
  rw [directStateBlock131_checked]
  rw [directStateBlock132_checked]
  rw [directStateBlock133_checked]
  rw [directStateBlock134_checked]
  rw [directStateBlock135_checked]
  rw [directStateBlock136_checked]
  rw [directStateBlock137_checked]
  rw [directStateBlock138_checked]
  rw [directStateBlock139_checked]
  rw [directStateBlock140_checked]
  rw [directStateBlock141_checked]
  rw [directStateBlock142_checked]
  rw [directStateBlock143_checked]
  rw [directStateBlock144_checked]
  rw [directStateBlock145_checked]
  rw [directStateBlock146_checked]
  rw [directStateBlock147_checked]
  rw [directStateBlock148_checked]
  rw [directStateBlock149_checked]
  rw [directStateBlock150_checked]
  rw [directStateBlock151_checked]
  rw [directStateBlock152_checked]
  rw [directStateBlock153_checked]
  rw [directStateBlock154_checked]
  rw [directStateBlock155_checked]
  rw [directStateBlock156_checked]
  rw [directStateBlock157_checked]
  rw [directStateBlock158_checked]
  rw [directStateBlock159_checked]
  rw [directStateBlock160_checked]
  rw [directStateBlock161_checked]
  rw [directStateBlock162_checked]
  rw [directStateBlock163_checked]
  rw [directStateBlock164_checked]
  rw [directStateBlock165_checked]
  rw [directStateBlock166_checked]
  rw [directStateBlock167_checked]
  rw [directStateBlock168_checked]
  rw [directStateBlock169_checked]
  rw [directStateBlock170_checked]
  rw [directStateBlock171_checked]
  rw [directStateBlock172_checked]
  rw [directStateBlock173_checked]
  rw [directStateBlock174_checked]
  rw [directStateBlock175_checked]
  rw [directStateBlock176_checked]
  rw [directStateBlock177_checked]
  rw [directStateBlock178_checked]
  rw [directStateBlock179_checked]
  rw [directStateBlock180_checked]
  rw [directStateBlock181_checked]
  rw [directStateBlock182_checked]
  rw [directStateBlock183_checked]
  rw [directStateBlock184_checked]
  rw [directStateBlock185_checked]
  rw [directStateBlock186_checked]
  rw [directStateBlock187_checked]
  rw [directStateBlock188_checked]
  rw [directStateBlock189_checked]
  rw [directStateBlock190_checked]
  rw [directStateBlock191_checked]
  rw [directStateBlock192_checked]
  rw [directStateBlock193_checked]
  rw [directStateBlock194_checked]
  rw [directStateBlock195_checked]
  rw [directStateBlock196_checked]
  rw [directStateBlock197_checked]
  rw [directStateBlock198_checked]
  rw [directStateBlock199_checked]
  rw [directStateBlock200_checked]
  rw [directStateBlock201_checked]
  rw [directStateBlock202_checked]
  rw [directStateBlock203_checked]
  rw [directStateBlock204_checked]
  rw [directStateBlock205_checked]
  rw [directStateBlock206_checked]
  rw [directStateBlock207_checked]
  rw [directStateBlock208_checked]
  rw [directStateBlock209_checked]
  rw [directStateBlock210_checked]
  rw [directStateBlock211_checked]
  rw [directStateBlock212_checked]
  rw [directStateBlock213_checked]
  rw [directStateBlock214_checked]
  rw [directStateBlock215_checked]
  rw [directStateBlock216_checked]
  rw [directStateBlock217_checked]
  rw [directStateBlock218_checked]
  rw [directStateBlock219_checked]
  rw [directStateBlock220_checked]
  rw [directStateBlock221_checked]
  rw [directStateBlock222_checked]
  rw [directStateBlock223_checked]
  rw [directStateBlock224_checked]
  rw [directStateBlock225_checked]
  rw [directStateBlock226_checked]
  rw [directStateBlock227_checked]
  rw [directStateBlock228_checked]
  rw [directStateBlock229_checked]
  rw [directStateBlock230_checked]
  rw [directStateBlock231_checked]
  rw [directStateBlock232_checked]
  rw [directStateBlock233_checked]
  rw [directStateBlock234_checked]
  rw [directStateBlock235_checked]
  rw [directStateBlock236_checked]
  rw [directStateBlock237_checked]
  rw [directStateBlock238_checked]
  rw [directStateBlock239_checked]
  rw [directStateBlock240_checked]
  rw [directStateBlock241_checked]
  rw [directStateBlock242_checked]
  rw [directStateBlock243_checked]
  rw [directStateBlock244_checked]
  rw [directStateBlock245_checked]
  rw [directStateBlock246_checked]
  rw [directStateBlock247_checked]
  rw [directStateBlock248_checked]
  rw [directStateBlock249_checked]
  rw [directStateBlock250_checked]
  rw [directStateBlock251_checked]
  rw [directStateBlock252_checked]
  rw [directStateBlock253_checked]
  rw [directStateBlock254_checked]
  rw [directStateBlock255_checked]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem generatedDirectStateSum_eq_generatedRawMomentPoly :
    generatedDirectStateSum = generatedRawMomentPoly := by
  rfl

theorem rawMomentPolyStateSum_eq_rawMomentPoly :
    rawMomentPolyStateSum = rawMomentPoly := by
  rw [rawMomentPolyStateSum_eq_generatedDirectStateSum,
    generatedDirectStateSum_eq_generatedRawMomentPoly,
    rawMomentPoly_eq_generated]

theorem eval_rawMomentPolyStateSum_eq_rawMomentPoly (X Y : Real) :
    rawMomentPolyStateSum.eval X Y = rawMomentPoly.eval X Y := by
  rw [rawMomentPolyStateSum_eq_rawMomentPoly]

end StatMech.FrontierA.NOneSymmetricMeanCertificate
