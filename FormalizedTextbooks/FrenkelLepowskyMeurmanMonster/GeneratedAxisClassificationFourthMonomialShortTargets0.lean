/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation

/-! Candidate full signed short-image addresses for original corrected monomial word 0.
They assert no correctness until checked against the actual Q images and numerators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000
-- Each candidate row has at most64 literal addresses; row names bound vector elaboration.

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row0 : Fin 64 → ℕ :=
  ![4096, 12300, 4106, 12294, 12297, 4101, 12291, 4111,
    4104, 12292, 4098, 12302, 12289, 4109, 12299, 4103,
    4120, 12308, 4114, 12318, 12305, 4125, 12315, 4119,
    4112, 12316, 4122, 12310, 12313, 4117, 12307, 4127,
    4136, 12324, 4130, 12334, 12321, 4141, 12331, 4135,
    4128, 12332, 4138, 12326, 12329, 4133, 12323, 4143,
    4144, 12348, 4154, 12342, 12345, 4149, 12339, 4159,
    4152, 12340, 4146, 12350, 12337, 4157, 12347, 4151]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row1 : Fin 64 → ℕ :=
  ![5696, 13920, 13924, 5700, 5744, 13904, 13908, 5748,
    5730, 13890, 13894, 5734, 5714, 13938, 13942, 5718,
    5736, 13896, 13900, 5740, 5720, 13944, 13948, 5724,
    5706, 13930, 13934, 5710, 5754, 13914, 13918, 5758,
    5729, 13889, 13893, 5733, 5713, 13937, 13941, 5717,
    5699, 13923, 13927, 5703, 5747, 13907, 13911, 5751,
    5705, 13929, 13933, 5709, 5753, 13913, 13917, 5757,
    5739, 13899, 13903, 5743, 5723, 13947, 13951, 5727]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row2 : Fin 64 → ℕ :=
  ![5760, 13964, 5815, 14011, 5770, 13958, 5821, 14001,
    13976, 5780, 13999, 5795, 13970, 5790, 13989, 5801,
    13960, 5764, 14015, 5811, 13954, 5774, 14005, 5817,
    5776, 13980, 5799, 13995, 5786, 13974, 5805, 13985,
    5769, 13957, 5822, 14002, 5763, 13967, 5812, 14008,
    13969, 5789, 13990, 5802, 13979, 5783, 13996, 5792,
    13953, 5773, 14006, 5818, 13963, 5767, 14012, 5808,
    5785, 13973, 5806, 13986, 5779, 13983, 5796, 13992]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row3 : Fin 64 → ℕ :=
  ![5312, 5318, 13538, 13540, 13507, 13509, 5345, 5351,
    13522, 13524, 5360, 5366, 5329, 5335, 13555, 13557,
    13514, 13516, 5352, 5358, 5321, 5327, 13547, 13549,
    5336, 5342, 13562, 13564, 13531, 13533, 5369, 5375,
    13506, 13508, 5344, 5350, 5313, 5319, 13539, 13541,
    5328, 5334, 13554, 13556, 13523, 13525, 5361, 5367,
    5320, 5326, 13546, 13548, 13515, 13517, 5353, 5359,
    13530, 13532, 5368, 5374, 5337, 5343, 13563, 13565]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row4 : Fin 64 → ℕ :=
  ![5376, 13616, 5400, 13608, 13584, 5408, 13576, 5432,
    13586, 5410, 13578, 5434, 5378, 13618, 5402, 13610,
    5396, 13604, 5388, 13628, 13572, 5428, 13596, 5420,
    13574, 5430, 13598, 5422, 5398, 13606, 5390, 13630,
    5423, 13599, 5431, 13575, 13631, 5391, 13607, 5399,
    13629, 5389, 13605, 5397, 5421, 13597, 5429, 13573,
    5435, 13579, 5411, 13587, 13611, 5403, 13619, 5379,
    13609, 5401, 13617, 5377, 5433, 13577, 5409, 13585]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row5 : Fin 64 → ℕ :=
  ![4416, 4428, 12628, 12632, 4420, 4424, 12624, 12636,
    4421, 4425, 12625, 12637, 4417, 4429, 12629, 12633,
    12614, 12618, 4434, 4446, 12610, 12622, 4438, 4442,
    12611, 12623, 4439, 4443, 12615, 12619, 4435, 4447,
    12667, 12663, 4463, 4451, 12671, 12659, 4459, 4455,
    12670, 12658, 4458, 4454, 12666, 12662, 4462, 4450,
    4477, 4465, 12649, 12645, 4473, 4469, 12653, 12641,
    4472, 4468, 12652, 12640, 4476, 4464, 12648, 12644]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row6 : Fin 64 → ℕ :=
  ![4480, 12735, 4482, 12733, 4484, 12731, 4486, 12729,
    4496, 12719, 4498, 12717, 4500, 12715, 4502, 12713,
    4488, 12727, 4490, 12725, 4492, 12723, 4494, 12721,
    4504, 12711, 4506, 12709, 4508, 12707, 4510, 12705,
    4512, 12703, 4514, 12701, 4516, 12699, 4518, 12697,
    4528, 12687, 4530, 12685, 4532, 12683, 4534, 12681,
    4520, 12695, 4522, 12693, 4524, 12691, 4526, 12689,
    4536, 12679, 4538, 12677, 4540, 12675, 4542, 12673]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row7 : Fin 64 → ℕ :=
  ![13120, 13129, 4931, 4938, 13121, 13128, 4930, 4939,
    4945, 4952, 13138, 13147, 4944, 4953, 13139, 13146,
    4961, 4968, 13154, 13163, 4960, 4969, 13155, 13162,
    13168, 13177, 4979, 4986, 13169, 13176, 4978, 4987,
    4990, 4983, 13181, 13172, 4991, 4982, 13180, 13173,
    13167, 13158, 4972, 4965, 13166, 13159, 4973, 4964,
    13151, 13142, 4956, 4949, 13150, 13143, 4957, 4948,
    4942, 4935, 13133, 13124, 4943, 4934, 13132, 13125]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row8 : Fin 64 → ℕ :=
  ![13184, 5055, 13200, 5039, 13188, 5051, 13204, 5035,
    4993, 13246, 5009, 13230, 4997, 13242, 5013, 13226,
    13192, 5047, 13208, 5031, 13196, 5043, 13212, 5027,
    5001, 13238, 5017, 13222, 5005, 13234, 5021, 13218,
    13186, 5053, 13202, 5037, 13190, 5049, 13206, 5033,
    4995, 13244, 5011, 13228, 4999, 13240, 5015, 13224,
    13194, 5045, 13210, 5029, 13198, 5041, 13214, 5025,
    5003, 13236, 5019, 13220, 5007, 13232, 5023, 13216]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row9 : Fin 64 → ℕ :=
  ![14016, 5828, 14018, 5830, 5887, 14075, 5885, 14073,
    14032, 5844, 14034, 5846, 5871, 14059, 5869, 14057,
    14024, 5836, 14026, 5838, 5879, 14067, 5877, 14065,
    14040, 5852, 14042, 5854, 5863, 14051, 5861, 14049,
    14017, 5829, 14019, 5831, 5886, 14074, 5884, 14072,
    14033, 5845, 14035, 5847, 5870, 14058, 5868, 14056,
    14025, 5837, 14027, 5839, 5878, 14066, 5876, 14064,
    14041, 5853, 14043, 5855, 5862, 14050, 5860, 14048]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row10 : Fin 64 → ℕ :=
  ![14080, 14081, 5905, 5904, 5893, 5892, 14100, 14101,
    14083, 14082, 5906, 5907, 5894, 5895, 14103, 14102,
    5921, 5920, 14128, 14129, 14116, 14117, 5941, 5940,
    5922, 5923, 14131, 14130, 14119, 14118, 5942, 5943,
    5950, 5951, 14127, 14126, 14139, 14138, 5930, 5931,
    5949, 5948, 14124, 14125, 14136, 14137, 5929, 5928,
    14111, 14110, 5902, 5903, 5914, 5915, 14091, 14090,
    14108, 14109, 5901, 5900, 5913, 5912, 14088, 14089]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row11 : Fin 64 → ℕ :=
  ![5440, 5448, 13642, 13634, 13644, 13636, 5446, 5454,
    13656, 13648, 5458, 5466, 5460, 5468, 13662, 13654,
    13641, 13633, 5443, 5451, 5445, 5453, 13647, 13639,
    5457, 5465, 13659, 13651, 13661, 13653, 5463, 5471,
    13687, 13695, 5501, 5493, 5499, 5491, 13681, 13689,
    5487, 5479, 13669, 13677, 13667, 13675, 5481, 5473,
    5502, 5494, 13684, 13692, 13682, 13690, 5496, 5488,
    13670, 13678, 5484, 5476, 5482, 5474, 13664, 13672]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row12 : Fin 64 → ℕ :=
  ![5504, 13700, 5520, 13716, 13759, 5563, 13743, 5547,
    13698, 5510, 13714, 5526, 5565, 13753, 5549, 13737,
    5512, 13708, 5528, 13724, 13751, 5555, 13735, 5539,
    13706, 5518, 13722, 5534, 5557, 13745, 5541, 13729,
    5536, 13732, 5552, 13748, 13727, 5531, 13711, 5515,
    13730, 5542, 13746, 5558, 5533, 13721, 5517, 13705,
    5544, 13740, 5560, 13756, 13719, 5523, 13703, 5507,
    13738, 5550, 13754, 5566, 5525, 13713, 5509, 13697]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row13 : Fin 64 → ℕ :=
  ![12736, 12740, 4550, 4546, 12795, 12799, 4605, 4601,
    12741, 12737, 4547, 4551, 12798, 12794, 4600, 4604,
    4556, 4552, 12746, 12750, 4599, 4595, 12785, 12789,
    4553, 4557, 12751, 12747, 4594, 4598, 12788, 12784,
    4564, 4560, 12754, 12758, 4591, 4587, 12777, 12781,
    4561, 4565, 12759, 12755, 4586, 4590, 12780, 12776,
    12760, 12764, 4574, 4570, 12771, 12775, 4581, 4577,
    12765, 12761, 4571, 4575, 12774, 12770, 4576, 4580]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row14 : Fin 64 → ℕ :=
  ![12800, 4616, 12832, 4648, 12804, 4620, 12836, 4652,
    12816, 4632, 12848, 4664, 12820, 4636, 12852, 4668,
    12802, 4618, 12834, 4650, 12806, 4622, 12838, 4654,
    12818, 4634, 12850, 4666, 12822, 4638, 12854, 4670,
    12863, 4663, 12831, 4631, 12859, 4659, 12827, 4627,
    12847, 4647, 12815, 4615, 12843, 4643, 12811, 4611,
    12861, 4661, 12829, 4629, 12857, 4657, 12825, 4625,
    12845, 4645, 12813, 4613, 12841, 4641, 12809, 4609]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row15 : Fin 64 → ℕ :=
  ![5056, 5057, 13281, 13280, 5118, 5119, 13279, 13278,
    13265, 13264, 5104, 5105, 13295, 13294, 5070, 5071,
    13257, 13256, 5096, 5097, 13303, 13302, 5078, 5079,
    5080, 5081, 13305, 13304, 5094, 5095, 13255, 13254,
    13251, 13250, 5090, 5091, 13309, 13308, 5084, 5085,
    5074, 5075, 13299, 13298, 5100, 5101, 13261, 13260,
    5066, 5067, 13291, 13290, 5108, 5109, 13269, 13268,
    13275, 13274, 5114, 5115, 13285, 13284, 5060, 5061]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row16 : Fin 64 → ℕ :=
  ![5120, 13320, 5122, 13322, 5124, 13324, 5126, 13326,
    13313, 5129, 13315, 5131, 13317, 5133, 13319, 5135,
    5136, 13336, 5138, 13338, 5140, 13340, 5142, 13342,
    13329, 5145, 13331, 5147, 13333, 5149, 13335, 5151,
    5183, 13367, 5181, 13365, 5179, 13363, 5177, 13361,
    13374, 5174, 13372, 5172, 13370, 5170, 13368, 5168,
    5167, 13351, 5165, 13349, 5163, 13347, 5161, 13345,
    13358, 5158, 13356, 5156, 13354, 5154, 13352, 5152]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row17 : Fin 64 → ℕ :=
  ![14144, 6000, 14162, 5986, 5968, 14176, 5954, 14194,
    14161, 5985, 14147, 6003, 5953, 14193, 5971, 14179,
    14164, 5988, 14150, 6006, 5956, 14196, 5974, 14182,
    14149, 6005, 14167, 5991, 5973, 14181, 5959, 14199,
    14191, 5983, 14205, 5965, 6015, 14159, 5997, 14173,
    14206, 5966, 14188, 5980, 5998, 14174, 6012, 14156,
    14203, 5963, 14185, 5977, 5995, 14171, 6009, 14153,
    14186, 5978, 14200, 5960, 6010, 14154, 5992, 14168]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row18 : Fin 64 → ℕ :=
  ![14208, 14209, 6025, 6024, 6033, 6032, 14232, 14233,
    14211, 14210, 6026, 6027, 6034, 6035, 14235, 14234,
    6078, 6079, 14263, 14262, 14255, 14254, 6054, 6055,
    6077, 6076, 14260, 14261, 14252, 14253, 6053, 6052,
    6021, 6020, 14220, 14221, 14228, 14229, 6045, 6044,
    6022, 6023, 14223, 14222, 14231, 14230, 6046, 6047,
    14267, 14266, 6066, 6067, 6058, 6059, 14243, 14242,
    14264, 14265, 6065, 6064, 6057, 6056, 14240, 14241]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row19 : Fin 64 → ℕ :=
  ![4288, 4324, 12512, 12484, 12513, 12485, 4289, 4325,
    4336, 4308, 12496, 12532, 12497, 12533, 4337, 4309,
    4328, 4300, 12488, 12524, 12489, 12525, 4329, 4301,
    4312, 4348, 12536, 12508, 12537, 12509, 4313, 4349,
    4322, 4294, 12482, 12518, 12483, 12519, 4323, 4295,
    4306, 4342, 12530, 12502, 12531, 12503, 4307, 4343,
    4298, 4334, 12522, 12494, 12523, 12495, 4299, 4335,
    4346, 4318, 12506, 12542, 12507, 12543, 4347, 4319]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row20 : Fin 64 → ℕ :=
  ![4352, 4411, 4364, 4407, 12564, 12591, 12568, 12579,
    12550, 12605, 12554, 12593, 4370, 4393, 4382, 4389,
    12548, 12607, 12552, 12595, 4368, 4395, 4380, 4391,
    4354, 4409, 4366, 4405, 12566, 12589, 12570, 12577,
    4357, 4414, 4361, 4402, 12561, 12586, 12573, 12582,
    12547, 12600, 12559, 12596, 4375, 4396, 4379, 4384,
    12545, 12602, 12557, 12598, 4373, 4398, 4377, 4386,
    4359, 4412, 4363, 4400, 12563, 12584, 12575, 12580]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row21 : Fin 64 → ℕ :=
  ![4800, 13009, 12995, 4818, 12997, 4820, 4806, 13015,
    4801, 13008, 12994, 4819, 12996, 4821, 4807, 13014,
    13001, 4824, 4810, 13019, 4812, 13021, 13007, 4830,
    13000, 4825, 4811, 13018, 4813, 13020, 13006, 4831,
    13054, 4847, 4861, 13036, 4859, 13034, 13048, 4841,
    13055, 4846, 4860, 13037, 4858, 13035, 13049, 4840,
    4855, 13030, 13044, 4837, 13042, 4835, 4849, 13024,
    4854, 13031, 13045, 4836, 13043, 4834, 4848, 13025]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row22 : Fin 64 → ℕ :=
  ![4864, 13119, 13064, 4919, 13057, 4926, 4873, 13110,
    4880, 13103, 13080, 4903, 13073, 4910, 4889, 13094,
    4866, 13117, 13066, 4917, 13059, 4924, 4875, 13108,
    4882, 13101, 13082, 4901, 13075, 4908, 4891, 13092,
    4896, 13087, 13096, 4887, 13089, 4894, 4905, 13078,
    4912, 13071, 13112, 4871, 13105, 4878, 4921, 13062,
    4898, 13085, 13098, 4885, 13091, 4892, 4907, 13076,
    4914, 13069, 13114, 4869, 13107, 4876, 4923, 13060]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row23 : Fin 64 → ℕ :=
  ![5568, 5584, 5570, 5586, 5572, 5588, 5574, 5590,
    13823, 13807, 13821, 13805, 13819, 13803, 13817, 13801,
    5569, 5585, 5571, 5587, 5573, 5589, 5575, 5591,
    13822, 13806, 13820, 13804, 13818, 13802, 13816, 13800,
    5600, 5616, 5602, 5618, 5604, 5620, 5606, 5622,
    13791, 13775, 13789, 13773, 13787, 13771, 13785, 13769,
    5601, 5617, 5603, 5619, 5605, 5621, 5607, 5623,
    13790, 13774, 13788, 13772, 13786, 13770, 13784, 13768]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row24 : Fin 64 → ℕ :=
  ![5632, 5633, 5637, 5636, 5635, 5634, 5638, 5639,
    13841, 13840, 13844, 13845, 13842, 13843, 13847, 13846,
    13833, 13832, 13836, 13837, 13834, 13835, 13839, 13838,
    5656, 5657, 5661, 5660, 5659, 5658, 5662, 5663,
    13886, 13887, 13883, 13882, 13885, 13884, 13880, 13881,
    5679, 5678, 5674, 5675, 5676, 5677, 5673, 5672,
    5687, 5686, 5682, 5683, 5684, 5685, 5681, 5680,
    13862, 13863, 13859, 13858, 13861, 13860, 13856, 13857]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row25 : Fin 64 → ℕ :=
  ![4160, 12385, 12361, 4200, 4163, 12386, 12362, 4203,
    12369, 4208, 4184, 12409, 12370, 4211, 4187, 12410,
    12357, 4196, 4172, 12397, 12358, 4199, 4175, 12398,
    4180, 12405, 12381, 4220, 4183, 12406, 12382, 4223,
    12353, 4192, 4168, 12393, 12354, 4195, 4171, 12394,
    4176, 12401, 12377, 4216, 4179, 12402, 12378, 4219,
    4164, 12389, 12365, 4204, 4167, 12390, 12366, 4207,
    12373, 4212, 4188, 12413, 12374, 4215, 4191, 12414]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row26 : Fin 64 → ℕ :=
  ![4224, 12464, 12436, 4260, 4241, 12449, 12421, 4277,
    12432, 4256, 4228, 12468, 12417, 4273, 4245, 12453,
    4248, 12456, 12428, 4284, 4233, 12473, 12445, 4269,
    12424, 4280, 4252, 12460, 12441, 4265, 4237, 12477,
    4271, 12447, 12475, 4235, 4286, 12430, 12458, 4250,
    12479, 4239, 4267, 12443, 12462, 4254, 4282, 12426,
    4279, 12423, 12451, 4243, 4262, 12438, 12466, 4226,
    12455, 4247, 4275, 12419, 12470, 4230, 4258, 12434]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row27 : Fin 64 → ℕ :=
  ![12864, 12896, 12866, 12898, 4673, 4705, 4675, 4707,
    12880, 12912, 12882, 12914, 4689, 4721, 4691, 4723,
    12872, 12904, 12874, 12906, 4681, 4713, 4683, 4715,
    12888, 12920, 12890, 12922, 4697, 4729, 4699, 4731,
    12927, 12895, 12925, 12893, 4734, 4702, 4732, 4700,
    12911, 12879, 12909, 12877, 4718, 4686, 4716, 4684,
    12919, 12887, 12917, 12885, 4726, 4694, 4724, 4692,
    12903, 12871, 12901, 12869, 4710, 4678, 4708, 4676]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row28 : Fin 64 → ℕ :=
  ![12928, 12929, 12937, 12936, 4741, 4740, 4748, 4749,
    12990, 12991, 12983, 12982, 4795, 4794, 4786, 4787,
    4739, 4738, 4746, 4747, 12934, 12935, 12943, 12942,
    4797, 4796, 4788, 4789, 12984, 12985, 12977, 12976,
    4753, 4752, 4760, 4761, 12948, 12949, 12957, 12956,
    4783, 4782, 4774, 4775, 12970, 12971, 12963, 12962,
    12946, 12947, 12955, 12954, 4759, 4758, 4766, 4767,
    12972, 12973, 12965, 12964, 4777, 4776, 4768, 4769]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row29 : Fin 64 → ℕ :=
  ![13376, 5196, 5190, 13386, 5204, 13400, 13394, 5214,
    5243, 13431, 13437, 5233, 13423, 5219, 5225, 13413,
    5188, 13384, 13378, 5198, 13392, 5212, 5206, 13402,
    13439, 5235, 5241, 13429, 5227, 13415, 13421, 5217,
    13381, 5193, 5187, 13391, 5201, 13405, 13399, 5211,
    5246, 13426, 13432, 5236, 13418, 5222, 5228, 13408,
    5185, 13389, 13383, 5195, 13397, 5209, 5203, 13407,
    13434, 5238, 5244, 13424, 5230, 13410, 13416, 5220]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row30 : Fin 64 → ℕ :=
  ![13440, 13441, 13449, 13448, 5281, 5280, 5288, 5289,
    5251, 5250, 5258, 5259, 13474, 13475, 13483, 13482,
    5253, 5252, 5260, 5261, 13476, 13477, 13485, 13484,
    13446, 13447, 13455, 13454, 5287, 5286, 5294, 5295,
    13502, 13503, 13495, 13494, 5279, 5278, 5270, 5271,
    5309, 5308, 5300, 5301, 13468, 13469, 13461, 13460,
    5307, 5306, 5298, 5299, 13466, 13467, 13459, 13458,
    13496, 13497, 13489, 13488, 5273, 5272, 5264, 5265]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row31 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6084, 14331, 14308, 6107,
    6088, 14327, 14312, 6103, 0, 0, 0, 0,
    0, 0, 0, 0, 6100, 14315, 14324, 6091,
    6104, 14311, 14328, 6087, 0, 0, 0, 0,
    0, 0, 0, 0, 14278, 6137, 6118, 14297,
    14282, 6133, 6122, 14293, 0, 0, 0, 0,
    0, 0, 0, 0, 14294, 6121, 6134, 14281,
    14298, 6117, 6138, 14277, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row32 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6084, 14331, 14308, 6107,
    6088, 14327, 14312, 6103, 0, 0, 0, 0,
    0, 0, 0, 0, 6100, 14315, 14324, 6091,
    6104, 14311, 14328, 6087, 0, 0, 0, 0,
    0, 0, 0, 0, 14278, 6137, 6118, 14297,
    14282, 6133, 6122, 14293, 0, 0, 0, 0,
    0, 0, 0, 0, 14294, 6121, 6134, 14281,
    14298, 6117, 6138, 14277, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row33 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7365, 7380, 15556, 15573,
    7369, 7384, 15560, 15577, 0, 0, 0, 0,
    0, 0, 0, 0, 15588, 15605, 7397, 7412,
    15592, 15609, 7401, 7416, 0, 0, 0, 0,
    0, 0, 0, 0, 15558, 15575, 7367, 7382,
    15562, 15579, 7371, 7386, 0, 0, 0, 0,
    0, 0, 0, 0, 7399, 7414, 15590, 15607,
    7403, 7418, 15594, 15611, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row34 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7365, 7380, 15556, 15573,
    7369, 7384, 15560, 15577, 0, 0, 0, 0,
    0, 0, 0, 0, 15588, 15605, 7397, 7412,
    15592, 15609, 7401, 7416, 0, 0, 0, 0,
    0, 0, 0, 0, 15558, 15575, 7367, 7382,
    15562, 15579, 7371, 7386, 0, 0, 0, 0,
    0, 0, 0, 0, 7399, 7414, 15590, 15607,
    7403, 7418, 15594, 15611, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row35 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14533, 14532, 6342, 6343,
    14537, 14536, 6346, 6347, 0, 0, 0, 0,
    0, 0, 0, 0, 6356, 6357, 14551, 14550,
    6360, 6361, 14555, 14554, 0, 0, 0, 0,
    0, 0, 0, 0, 6395, 6394, 14584, 14585,
    6391, 6390, 14580, 14581, 0, 0, 0, 0,
    0, 0, 0, 0, 14570, 14571, 6377, 6376,
    14566, 14567, 6373, 6372, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row36 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14533, 14532, 6342, 6343,
    14537, 14536, 6346, 6347, 0, 0, 0, 0,
    0, 0, 0, 0, 6356, 6357, 14551, 14550,
    6360, 6361, 14555, 14554, 0, 0, 0, 0,
    0, 0, 0, 0, 6395, 6394, 14584, 14585,
    6391, 6390, 14580, 14581, 0, 0, 0, 0,
    0, 0, 0, 0, 14570, 14571, 6377, 6376,
    14566, 14567, 6373, 6372, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row37 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15301, 15297, 15305, 15309,
    15302, 15298, 15306, 15310, 0, 0, 0, 0,
    0, 0, 0, 0, 15358, 15354, 15346, 15350,
    15357, 15353, 15345, 15349, 0, 0, 0, 0,
    0, 0, 0, 0, 7121, 7125, 7133, 7129,
    7122, 7126, 7134, 7130, 0, 0, 0, 0,
    0, 0, 0, 0, 7146, 7150, 7142, 7138,
    7145, 7149, 7141, 7137, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row38 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15301, 15297, 15305, 15309,
    15302, 15298, 15306, 15310, 0, 0, 0, 0,
    0, 0, 0, 0, 15358, 15354, 15346, 15350,
    15357, 15353, 15345, 15349, 0, 0, 0, 0,
    0, 0, 0, 0, 7121, 7125, 7133, 7129,
    7122, 7126, 7134, 7130, 0, 0, 0, 0,
    0, 0, 0, 0, 7146, 7150, 7142, 7138,
    7145, 7149, 7141, 7137, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row39 : Fin 64 → ℕ :=
  ![0, 6853, 6857, 0, 0, 15060, 15064, 0,
    0, 15044, 15048, 0, 0, 6869, 6873, 0,
    0, 15046, 15050, 0, 0, 6871, 6875, 0,
    0, 6855, 6859, 0, 0, 15062, 15066, 0,
    0, 15099, 15095, 0, 0, 6890, 6886, 0,
    0, 6906, 6902, 0, 0, 15083, 15079, 0,
    0, 6904, 6900, 0, 0, 15081, 15077, 0,
    0, 15097, 15093, 0, 0, 6888, 6884, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row40 : Fin 64 → ℕ :=
  ![0, 6853, 6857, 0, 0, 15060, 15064, 0,
    0, 15044, 15048, 0, 0, 6869, 6873, 0,
    0, 15046, 15050, 0, 0, 6871, 6875, 0,
    0, 6855, 6859, 0, 0, 15062, 15066, 0,
    0, 15099, 15095, 0, 0, 6890, 6886, 0,
    0, 6906, 6902, 0, 0, 15083, 15079, 0,
    0, 6904, 6900, 0, 0, 15081, 15077, 0,
    0, 15097, 15093, 0, 0, 6888, 6884, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row41 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15813, 7652, 15814, 7655,
    15817, 7656, 15818, 7659, 0, 0, 0, 0,
    0, 0, 0, 0, 15828, 7669, 15831, 7670,
    15832, 7673, 15835, 7674, 0, 0, 0, 0,
    0, 0, 0, 0, 7620, 15845, 7623, 15846,
    7624, 15849, 7627, 15850, 0, 0, 0, 0,
    0, 0, 0, 0, 7637, 15860, 7638, 15863,
    7641, 15864, 7642, 15867, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row42 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15813, 7652, 15814, 7655,
    15817, 7656, 15818, 7659, 0, 0, 0, 0,
    0, 0, 0, 0, 15828, 7669, 15831, 7670,
    15832, 7673, 15835, 7674, 0, 0, 0, 0,
    0, 0, 0, 0, 7620, 15845, 7623, 15846,
    7624, 15849, 7627, 15850, 0, 0, 0, 0,
    0, 0, 0, 0, 7637, 15860, 7638, 15863,
    7641, 15864, 7642, 15867, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row43 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14793, 6593, 14801, 6617,
    14794, 6594, 14802, 6618, 0, 0, 0, 0,
    0, 0, 0, 0, 14789, 6605, 14813, 6613,
    14790, 6606, 14814, 6614, 0, 0, 0, 0,
    0, 0, 0, 0, 6654, 14838, 6630, 14830,
    6653, 14837, 6629, 14829, 0, 0, 0, 0,
    0, 0, 0, 0, 6642, 14842, 6634, 14818,
    6641, 14841, 6633, 14817, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row44 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14793, 6593, 14801, 6617,
    14794, 6594, 14802, 6618, 0, 0, 0, 0,
    0, 0, 0, 0, 14789, 6605, 14813, 6613,
    14790, 6606, 14814, 6614, 0, 0, 0, 0,
    0, 0, 0, 0, 6654, 14838, 6630, 14830,
    6653, 14837, 6629, 14829, 0, 0, 0, 0,
    0, 0, 0, 0, 6642, 14842, 6634, 14818,
    6641, 14841, 6633, 14817, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row45 : Fin 64 → ℕ :=
  ![0, 7876, 7880, 0, 0, 16123, 16119, 0,
    0, 16069, 16073, 0, 0, 7930, 7926, 0,
    0, 7878, 7882, 0, 0, 16121, 16117, 0,
    0, 16071, 16075, 0, 0, 7928, 7924, 0,
    0, 7892, 7896, 0, 0, 16107, 16103, 0,
    0, 16085, 16089, 0, 0, 7914, 7910, 0,
    0, 7894, 7898, 0, 0, 16105, 16101, 0,
    0, 16087, 16091, 0, 0, 7912, 7908, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row46 : Fin 64 → ℕ :=
  ![0, 7876, 7880, 0, 0, 16123, 16119, 0,
    0, 16069, 16073, 0, 0, 7930, 7926, 0,
    0, 7878, 7882, 0, 0, 16121, 16117, 0,
    0, 16071, 16075, 0, 0, 7928, 7924, 0,
    0, 7892, 7896, 0, 0, 16107, 16103, 0,
    0, 16085, 16089, 0, 0, 7914, 7910, 0,
    0, 7894, 7898, 0, 0, 16105, 16101, 0,
    0, 16087, 16091, 0, 0, 7912, 7908, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row47 : Fin 64 → ℕ :=
  ![0, 14661, 14665, 0, 0, 14660, 14664, 0,
    0, 14662, 14666, 0, 0, 14663, 14667, 0,
    0, 6500, 6504, 0, 0, 6501, 6505, 0,
    0, 6503, 6507, 0, 0, 6502, 6506, 0,
    0, 6523, 6519, 0, 0, 6522, 6518, 0,
    0, 6520, 6516, 0, 0, 6521, 6517, 0,
    0, 14682, 14678, 0, 0, 14683, 14679, 0,
    0, 14681, 14677, 0, 0, 14680, 14676, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row48 : Fin 64 → ℕ :=
  ![0, 14661, 14665, 0, 0, 14660, 14664, 0,
    0, 14662, 14666, 0, 0, 14663, 14667, 0,
    0, 6500, 6504, 0, 0, 6501, 6505, 0,
    0, 6503, 6507, 0, 0, 6502, 6506, 0,
    0, 6523, 6519, 0, 0, 6522, 6518, 0,
    0, 6520, 6516, 0, 0, 6521, 6517, 0,
    0, 14682, 14678, 0, 0, 14683, 14679, 0,
    0, 14681, 14677, 0, 0, 14680, 14676, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row49 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7268, 15444, 7238, 15478,
    7272, 15448, 7242, 15482, 0, 0, 0, 0,
    0, 0, 0, 0, 15429, 7285, 15463, 7255,
    15433, 7289, 15467, 7259, 0, 0, 0, 0,
    0, 0, 0, 0, 7236, 15476, 7270, 15446,
    7240, 15480, 7274, 15450, 0, 0, 0, 0,
    0, 0, 0, 0, 15461, 7253, 15431, 7287,
    15465, 7257, 15435, 7291, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row50 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7268, 15444, 7238, 15478,
    7272, 15448, 7242, 15482, 0, 0, 0, 0,
    0, 0, 0, 0, 15429, 7285, 15463, 7255,
    15433, 7289, 15467, 7259, 0, 0, 0, 0,
    0, 0, 0, 0, 7236, 15476, 7270, 15446,
    7240, 15480, 7274, 15450, 0, 0, 0, 0,
    0, 0, 0, 0, 15461, 7253, 15431, 7287,
    15465, 7257, 15435, 7291, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row51 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14406, 6212, 14436, 6246,
    14410, 6216, 14440, 6250, 0, 0, 0, 0,
    0, 0, 0, 0, 6213, 14407, 6247, 14437,
    6217, 14411, 6251, 14441, 0, 0, 0, 0,
    0, 0, 0, 0, 14420, 6230, 14454, 6260,
    14424, 6234, 14458, 6264, 0, 0, 0, 0,
    0, 0, 0, 0, 6231, 14421, 6261, 14455,
    6235, 14425, 6265, 14459, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row52 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14406, 6212, 14436, 6246,
    14410, 6216, 14440, 6250, 0, 0, 0, 0,
    0, 0, 0, 0, 6213, 14407, 6247, 14437,
    6217, 14411, 6251, 14441, 0, 0, 0, 0,
    0, 0, 0, 0, 14420, 6230, 14454, 6260,
    14424, 6234, 14458, 6264, 0, 0, 0, 0,
    0, 0, 0, 0, 6231, 14421, 6261, 14455,
    6235, 14425, 6265, 14459, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row53 : Fin 64 → ℕ :=
  ![0, 7489, 7490, 0, 0, 7493, 7494, 0,
    0, 7505, 7506, 0, 0, 7509, 7510, 0,
    0, 7497, 7498, 0, 0, 7501, 7502, 0,
    0, 7513, 7514, 0, 0, 7517, 7518, 0,
    0, 7550, 7549, 0, 0, 7546, 7545, 0,
    0, 7534, 7533, 0, 0, 7530, 7529, 0,
    0, 7542, 7541, 0, 0, 7538, 7537, 0,
    0, 7526, 7525, 0, 0, 7522, 7521, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row54 : Fin 64 → ℕ :=
  ![0, 7489, 7490, 0, 0, 7493, 7494, 0,
    0, 7505, 7506, 0, 0, 7509, 7510, 0,
    0, 7497, 7498, 0, 0, 7501, 7502, 0,
    0, 7513, 7514, 0, 0, 7517, 7518, 0,
    0, 7550, 7549, 0, 0, 7546, 7545, 0,
    0, 7534, 7533, 0, 0, 7530, 7529, 0,
    0, 7542, 7541, 0, 0, 7538, 7537, 0,
    0, 7526, 7525, 0, 0, 7522, 7521, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row55 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6756, 14916, 14918, 6758,
    6760, 14920, 14922, 6762, 0, 0, 0, 0,
    0, 0, 0, 0, 14932, 6772, 6774, 14934,
    14936, 6776, 6778, 14938, 0, 0, 0, 0,
    0, 0, 0, 0, 6725, 14949, 14951, 6727,
    6729, 14953, 14955, 6731, 0, 0, 0, 0,
    0, 0, 0, 0, 14965, 6741, 6743, 14967,
    14969, 6745, 6747, 14971, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row56 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6756, 14916, 14918, 6758,
    6760, 14920, 14922, 6762, 0, 0, 0, 0,
    0, 0, 0, 0, 14932, 6772, 6774, 14934,
    14936, 6776, 6778, 14938, 0, 0, 0, 0,
    0, 0, 0, 0, 6725, 14949, 14951, 6727,
    6729, 14953, 14955, 6731, 0, 0, 0, 0,
    0, 0, 0, 0, 14965, 6741, 6743, 14967,
    14969, 6745, 6747, 14971, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row57 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 8004, 16251, 8006, 16249,
    8008, 16247, 8010, 16245, 0, 0, 0, 0,
    0, 0, 0, 0, 8036, 16219, 8038, 16217,
    8040, 16215, 8042, 16213, 0, 0, 0, 0,
    0, 0, 0, 0, 8005, 16250, 8007, 16248,
    8009, 16246, 8011, 16244, 0, 0, 0, 0,
    0, 0, 0, 0, 8037, 16218, 8039, 16216,
    8041, 16214, 8043, 16212, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row58 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 8004, 16251, 8006, 16249,
    8008, 16247, 8010, 16245, 0, 0, 0, 0,
    0, 0, 0, 0, 8036, 16219, 8038, 16217,
    8040, 16215, 8042, 16213, 0, 0, 0, 0,
    0, 0, 0, 0, 8005, 16250, 8007, 16248,
    8009, 16246, 8011, 16244, 0, 0, 0, 0,
    0, 0, 0, 0, 8037, 16218, 8039, 16216,
    8041, 16214, 8043, 16212, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row59 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6977, 15177, 6993, 15193,
    6978, 15178, 6994, 15194, 0, 0, 0, 0,
    0, 0, 0, 0, 7009, 15209, 7025, 15225,
    7010, 15210, 7026, 15226, 0, 0, 0, 0,
    0, 0, 0, 0, 7038, 15222, 7022, 15206,
    7037, 15221, 7021, 15205, 0, 0, 0, 0,
    0, 0, 0, 0, 7006, 15190, 6990, 15174,
    7005, 15189, 6989, 15173, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row60 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6977, 15177, 6993, 15193,
    6978, 15178, 6994, 15194, 0, 0, 0, 0,
    0, 0, 0, 0, 7009, 15209, 7025, 15225,
    7010, 15210, 7026, 15226, 0, 0, 0, 0,
    0, 0, 0, 0, 7038, 15222, 7022, 15206,
    7037, 15221, 7021, 15205, 0, 0, 0, 0,
    0, 0, 0, 0, 7006, 15190, 6990, 15174,
    7005, 15189, 6989, 15173, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row61 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7748, 7780, 7750, 7782,
    7752, 7784, 7754, 7786, 0, 0, 0, 0,
    0, 0, 0, 0, 15995, 15963, 15993, 15961,
    15991, 15959, 15989, 15957, 0, 0, 0, 0,
    0, 0, 0, 0, 7764, 7796, 7766, 7798,
    7768, 7800, 7770, 7802, 0, 0, 0, 0,
    0, 0, 0, 0, 15979, 15947, 15977, 15945,
    15975, 15943, 15973, 15941, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord0Row62 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7748, 7780, 7750, 7782,
    7752, 7784, 7754, 7786, 0, 0, 0, 0,
    0, 0, 0, 0, 15995, 15963, 15993, 15961,
    15991, 15959, 15989, 15957, 0, 0, 0, 0,
    0, 0, 0, 0, 7764, 7796, 7766, 7798,
    7768, 7800, 7770, 7802, 0, 0, 0, 0,
    0, 0, 0, 0, 15979, 15947, 15977, 15945,
    15975, 15943, 15973, 15941, 0, 0, 0, 0]

/-- Literal candidate octad target addresses, with the target central phase retained. -/
def generatedFourthMonomialShortOctadTargets0 : Fin 63 → Fin 64 → ℕ :=
  ![
    generatedFourthMonomialOctadWord0Row0,
    generatedFourthMonomialOctadWord0Row1,
    generatedFourthMonomialOctadWord0Row2,
    generatedFourthMonomialOctadWord0Row3,
    generatedFourthMonomialOctadWord0Row4,
    generatedFourthMonomialOctadWord0Row5,
    generatedFourthMonomialOctadWord0Row6,
    generatedFourthMonomialOctadWord0Row7,
    generatedFourthMonomialOctadWord0Row8,
    generatedFourthMonomialOctadWord0Row9,
    generatedFourthMonomialOctadWord0Row10,
    generatedFourthMonomialOctadWord0Row11,
    generatedFourthMonomialOctadWord0Row12,
    generatedFourthMonomialOctadWord0Row13,
    generatedFourthMonomialOctadWord0Row14,
    generatedFourthMonomialOctadWord0Row15,
    generatedFourthMonomialOctadWord0Row16,
    generatedFourthMonomialOctadWord0Row17,
    generatedFourthMonomialOctadWord0Row18,
    generatedFourthMonomialOctadWord0Row19,
    generatedFourthMonomialOctadWord0Row20,
    generatedFourthMonomialOctadWord0Row21,
    generatedFourthMonomialOctadWord0Row22,
    generatedFourthMonomialOctadWord0Row23,
    generatedFourthMonomialOctadWord0Row24,
    generatedFourthMonomialOctadWord0Row25,
    generatedFourthMonomialOctadWord0Row26,
    generatedFourthMonomialOctadWord0Row27,
    generatedFourthMonomialOctadWord0Row28,
    generatedFourthMonomialOctadWord0Row29,
    generatedFourthMonomialOctadWord0Row30,
    generatedFourthMonomialOctadWord0Row31,
    generatedFourthMonomialOctadWord0Row32,
    generatedFourthMonomialOctadWord0Row33,
    generatedFourthMonomialOctadWord0Row34,
    generatedFourthMonomialOctadWord0Row35,
    generatedFourthMonomialOctadWord0Row36,
    generatedFourthMonomialOctadWord0Row37,
    generatedFourthMonomialOctadWord0Row38,
    generatedFourthMonomialOctadWord0Row39,
    generatedFourthMonomialOctadWord0Row40,
    generatedFourthMonomialOctadWord0Row41,
    generatedFourthMonomialOctadWord0Row42,
    generatedFourthMonomialOctadWord0Row43,
    generatedFourthMonomialOctadWord0Row44,
    generatedFourthMonomialOctadWord0Row45,
    generatedFourthMonomialOctadWord0Row46,
    generatedFourthMonomialOctadWord0Row47,
    generatedFourthMonomialOctadWord0Row48,
    generatedFourthMonomialOctadWord0Row49,
    generatedFourthMonomialOctadWord0Row50,
    generatedFourthMonomialOctadWord0Row51,
    generatedFourthMonomialOctadWord0Row52,
    generatedFourthMonomialOctadWord0Row53,
    generatedFourthMonomialOctadWord0Row54,
    generatedFourthMonomialOctadWord0Row55,
    generatedFourthMonomialOctadWord0Row56,
    generatedFourthMonomialOctadWord0Row57,
    generatedFourthMonomialOctadWord0Row58,
    generatedFourthMonomialOctadWord0Row59,
    generatedFourthMonomialOctadWord0Row60,
    generatedFourthMonomialOctadWord0Row61,
    generatedFourthMonomialOctadWord0Row62
  ]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row0 : Fin 24 → ℕ :=
  ![0, 1036, 9234, 9206, 0, 0, 0, 0,
    0, 0, 0, 0, 9224, 1098, 1010, 9232,
    9230, 9204, 9236, 9338, 9240, 1008, 1034, 9238]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row1 : Fin 24 → ℕ :=
  ![0, 0, 9036, 8870, 0, 0, 0, 0,
    0, 0, 0, 0, 8888, 1084, 674, 8988,
    8940, 8868, 9084, 9324, 9180, 672, 698, 9132]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 822, 0, 0, 0, 0,
    0, 0, 0, 0, 840, 9282, 9010, 848,
    846, 820, 898, 1138, 994, 9008, 9034, 946]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 582, 9254, 8338, 774,
    726, 148, 870, 1110, 966, 8336, 8822, 918]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 8490, 296, 8684,
    8588, 8636, 8540, 8732, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 8440, 490,
    394, 442, 346, 538, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 8680,
    8584, 8632, 8536, 8728, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    496, 498, 494, 548, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 448, 398, 544, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 446, 546, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 542, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9272, 8770, 792,
    744, 580, 888, 1128, 984, 8768, 8840, 936]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1058, 9280,
    9278, 9252, 9284, 9340, 9288, 1056, 1082, 9286]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 8962,
    8914, 8290, 9058, 9298, 9154, 48, 626, 9106]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    798, 772, 896, 1136, 992, 8960, 8986, 944]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 724, 894, 1134, 990, 8912, 8938, 942]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 868, 1108, 964, 8288, 8820, 916]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1140, 996, 9056, 9082, 948]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1144, 9296, 9322, 1142]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9152, 9178, 998]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 624, 9104]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 9130]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign0Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row0 : Fin 24 → ℕ :=
  ![0, 1037, 9235, 9207, 0, 0, 0, 0,
    0, 0, 0, 0, 9225, 1099, 1011, 9233,
    9231, 9205, 9237, 9339, 9241, 1009, 1035, 9239]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row1 : Fin 24 → ℕ :=
  ![0, 0, 9037, 8871, 0, 0, 0, 0,
    0, 0, 0, 0, 8889, 1085, 675, 8989,
    8941, 8869, 9085, 9325, 9181, 673, 699, 9133]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 823, 0, 0, 0, 0,
    0, 0, 0, 0, 841, 9283, 9011, 849,
    847, 821, 899, 1139, 995, 9009, 9035, 947]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 583, 9255, 8339, 775,
    727, 149, 871, 1111, 967, 8337, 8823, 919]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 8491, 297, 8685,
    8589, 8637, 8541, 8733, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 8441, 491,
    395, 443, 347, 539, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 8681,
    8585, 8633, 8537, 8729, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    497, 499, 495, 549, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 449, 399, 545, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 447, 547, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 543, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9273, 8771, 793,
    745, 581, 889, 1129, 985, 8769, 8841, 937]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1059, 9281,
    9279, 9253, 9285, 9341, 9289, 1057, 1083, 9287]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 8963,
    8915, 8291, 9059, 9299, 9155, 49, 627, 9107]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    799, 773, 897, 1137, 993, 8961, 8987, 945]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 725, 895, 1135, 991, 8913, 8939, 943]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 869, 1109, 965, 8289, 8821, 917]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1141, 997, 9057, 9083, 949]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1145, 9297, 9323, 1143]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9153, 9179, 999]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 625, 9105]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 9131]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord0Sign1Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- Literal candidate pair target addresses for both original preferred signs. -/
def generatedFourthMonomialShortPairTargets0 : Fin 2 → Fin 24 → Fin 24 → ℕ :=
  ![
    ![generatedFourthMonomialPairWord0Sign0Row0,
    generatedFourthMonomialPairWord0Sign0Row1,
    generatedFourthMonomialPairWord0Sign0Row2,
    generatedFourthMonomialPairWord0Sign0Row3,
    generatedFourthMonomialPairWord0Sign0Row4,
    generatedFourthMonomialPairWord0Sign0Row5,
      generatedFourthMonomialPairWord0Sign0Row6,
    generatedFourthMonomialPairWord0Sign0Row7,
    generatedFourthMonomialPairWord0Sign0Row8,
    generatedFourthMonomialPairWord0Sign0Row9,
    generatedFourthMonomialPairWord0Sign0Row10,
    generatedFourthMonomialPairWord0Sign0Row11,
      generatedFourthMonomialPairWord0Sign0Row12,
    generatedFourthMonomialPairWord0Sign0Row13,
    generatedFourthMonomialPairWord0Sign0Row14,
    generatedFourthMonomialPairWord0Sign0Row15,
    generatedFourthMonomialPairWord0Sign0Row16,
    generatedFourthMonomialPairWord0Sign0Row17,
      generatedFourthMonomialPairWord0Sign0Row18,
    generatedFourthMonomialPairWord0Sign0Row19,
    generatedFourthMonomialPairWord0Sign0Row20,
    generatedFourthMonomialPairWord0Sign0Row21,
    generatedFourthMonomialPairWord0Sign0Row22,
    generatedFourthMonomialPairWord0Sign0Row23],
    ![generatedFourthMonomialPairWord0Sign1Row0,
    generatedFourthMonomialPairWord0Sign1Row1,
    generatedFourthMonomialPairWord0Sign1Row2,
    generatedFourthMonomialPairWord0Sign1Row3,
    generatedFourthMonomialPairWord0Sign1Row4,
    generatedFourthMonomialPairWord0Sign1Row5,
      generatedFourthMonomialPairWord0Sign1Row6,
    generatedFourthMonomialPairWord0Sign1Row7,
    generatedFourthMonomialPairWord0Sign1Row8,
    generatedFourthMonomialPairWord0Sign1Row9,
    generatedFourthMonomialPairWord0Sign1Row10,
    generatedFourthMonomialPairWord0Sign1Row11,
      generatedFourthMonomialPairWord0Sign1Row12,
    generatedFourthMonomialPairWord0Sign1Row13,
    generatedFourthMonomialPairWord0Sign1Row14,
    generatedFourthMonomialPairWord0Sign1Row15,
    generatedFourthMonomialPairWord0Sign1Row16,
    generatedFourthMonomialPairWord0Sign1Row17,
      generatedFourthMonomialPairWord0Sign1Row18,
    generatedFourthMonomialPairWord0Sign1Row19,
    generatedFourthMonomialPairWord0Sign1Row20,
    generatedFourthMonomialPairWord0Sign1Row21,
    generatedFourthMonomialPairWord0Sign1Row22,
    generatedFourthMonomialPairWord0Sign1Row23]
  ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
