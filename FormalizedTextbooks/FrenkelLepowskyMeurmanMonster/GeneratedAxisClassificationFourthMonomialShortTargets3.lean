/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation

/-! Candidate full signed short-image addresses for original corrected monomial word 3.
They assert no correctness until checked against the actual Q images and numerators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000
-- Each candidate row has at most64 literal addresses; row names bound vector elaboration.

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row0 : Fin 64 → ℕ :=
  ![4096, 4129, 4130, 4099, 4132, 4101, 4102, 4135,
    4136, 4105, 4106, 4139, 4108, 4141, 4142, 4111,
    12319, 12350, 12349, 12316, 12347, 12314, 12313, 12344,
    12343, 12310, 12309, 12340, 12307, 12338, 12337, 12304,
    4128, 4097, 4098, 4131, 4100, 4133, 4134, 4103,
    4104, 4137, 4138, 4107, 4140, 4109, 4110, 4143,
    12351, 12318, 12317, 12348, 12315, 12346, 12345, 12312,
    12311, 12342, 12341, 12308, 12339, 12306, 12305, 12336]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row1 : Fin 64 → ℕ :=
  ![4160, 12354, 12353, 4163, 4168, 12362, 12361, 4171,
    4164, 12358, 12357, 4167, 4172, 12366, 12365, 4175,
    4176, 12370, 12369, 4179, 4184, 12378, 12377, 4187,
    4180, 12374, 12373, 4183, 4188, 12382, 12381, 4191,
    4192, 12386, 12385, 4195, 4200, 12394, 12393, 4203,
    4196, 12390, 12389, 4199, 4204, 12398, 12397, 4207,
    4208, 12402, 12401, 4211, 4216, 12410, 12409, 4219,
    4212, 12406, 12405, 4215, 4220, 12414, 12413, 4223]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row2 : Fin 64 → ℕ :=
  ![4224, 12475, 4279, 12428, 12478, 4229, 12425, 4274,
    4285, 12422, 4234, 12465, 12419, 4280, 12468, 4239,
    12447, 4260, 12456, 4243, 4257, 12442, 4246, 12461,
    12450, 4249, 12437, 4270, 4252, 12455, 4267, 12432,
    12463, 4244, 12440, 4259, 4241, 12458, 4262, 12445,
    12434, 4265, 12453, 4254, 4268, 12439, 4251, 12448,
    4272, 12427, 4231, 12476, 12430, 4277, 12473, 4226,
    4237, 12470, 4282, 12417, 12467, 4232, 12420, 4287]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row3 : Fin 64 → ℕ :=
  ![4928, 4990, 13181, 13123, 13175, 13129, 4938, 4980,
    4987, 4933, 13126, 13176, 13132, 13170, 4977, 4943,
    13167, 13137, 4946, 4972, 4952, 4966, 13157, 13147,
    13140, 13162, 4969, 4951, 4963, 4957, 13150, 13152,
    13151, 13153, 4962, 4956, 4968, 4950, 13141, 13163,
    13156, 13146, 4953, 4967, 4947, 4973, 13166, 13136,
    4976, 4942, 13133, 13171, 13127, 13177, 4986, 4932,
    4939, 4981, 13174, 13128, 13180, 13122, 4929, 4991]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row4 : Fin 64 → ℕ :=
  ![4992, 13246, 5053, 13187, 13239, 5001, 13194, 5044,
    5051, 13189, 4998, 13240, 13196, 5042, 13233, 5007,
    5039, 13201, 5010, 13228, 13208, 5030, 13221, 5019,
    5012, 13226, 5033, 13207, 13219, 5021, 13214, 5024,
    5023, 13217, 5026, 13212, 13224, 5014, 13205, 5035,
    5028, 13210, 5017, 13223, 13203, 5037, 13230, 5008,
    5040, 13198, 5005, 13235, 13191, 5049, 13242, 4996,
    5003, 13237, 5046, 13192, 13244, 4994, 13185, 5055]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row5 : Fin 64 → ℕ :=
  ![4800, 4862, 13053, 12995, 4855, 4809, 13002, 13044,
    13051, 12997, 4806, 4856, 13004, 13042, 4849, 4815,
    13039, 13009, 4818, 4844, 13016, 13030, 4837, 4827,
    4820, 4842, 13033, 13015, 4835, 4829, 13022, 13024,
    13023, 13025, 4834, 4828, 13032, 13014, 4821, 4843,
    4836, 4826, 13017, 13031, 4819, 4845, 13038, 13008,
    4848, 4814, 13005, 13043, 4807, 4857, 13050, 12996,
    13003, 13045, 4854, 4808, 13052, 12994, 4801, 4863]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row6 : Fin 64 → ℕ :=
  ![4864, 13118, 4925, 13059, 4919, 13065, 4874, 13108,
    13115, 4869, 13062, 4920, 13068, 4914, 13105, 4879,
    4911, 13073, 4882, 13100, 4888, 13094, 4901, 13083,
    13076, 4906, 13097, 4887, 13091, 4893, 13086, 4896,
    4895, 13089, 4898, 13084, 4904, 13078, 4885, 13099,
    13092, 4890, 13081, 4903, 13075, 4909, 13102, 4880,
    4912, 13070, 4877, 13107, 4871, 13113, 4922, 13060,
    13067, 4917, 13110, 4872, 13116, 4866, 13057, 4927]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row7 : Fin 64 → ℕ :=
  ![5184, 13377, 5186, 13379, 13384, 5193, 13386, 5195,
    13380, 5189, 13382, 5191, 5196, 13389, 5198, 13391,
    5200, 13393, 5202, 13395, 13400, 5209, 13402, 5211,
    13396, 5205, 13398, 5207, 5212, 13405, 5214, 13407,
    5216, 13409, 5218, 13411, 13416, 5225, 13418, 5227,
    13412, 5221, 13414, 5223, 5228, 13421, 5230, 13423,
    5232, 13425, 5234, 13427, 13432, 5241, 13434, 5243,
    13428, 5237, 13430, 5239, 5244, 13437, 5246, 13439]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row8 : Fin 64 → ℕ :=
  ![5248, 13441, 5250, 13443, 5256, 13449, 5258, 13451,
    5252, 13445, 5254, 13447, 5260, 13453, 5262, 13455,
    5264, 13457, 5266, 13459, 5272, 13465, 5274, 13467,
    5268, 13461, 5270, 13463, 5276, 13469, 5278, 13471,
    5280, 13473, 5282, 13475, 5288, 13481, 5290, 13483,
    5284, 13477, 5286, 13479, 5292, 13485, 5294, 13487,
    5296, 13489, 5298, 13491, 5304, 13497, 5306, 13499,
    5300, 13493, 5302, 13495, 5308, 13501, 5310, 13503]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row9 : Fin 64 → ℕ :=
  ![5056, 13249, 5058, 13251, 13256, 5065, 13258, 5067,
    13252, 5061, 13254, 5063, 5068, 13261, 5070, 13263,
    5072, 13265, 5074, 13267, 13272, 5081, 13274, 5083,
    13268, 5077, 13270, 5079, 5084, 13277, 5086, 13279,
    5088, 13281, 5090, 13283, 13288, 5097, 13290, 5099,
    13284, 5093, 13286, 5095, 5100, 13293, 5102, 13295,
    5104, 13297, 5106, 13299, 13304, 5113, 13306, 5115,
    13300, 5109, 13302, 5111, 5116, 13309, 5118, 13311]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row10 : Fin 64 → ℕ :=
  ![5120, 13313, 5122, 13315, 5128, 13321, 5130, 13323,
    5124, 13317, 5126, 13319, 5132, 13325, 5134, 13327,
    5136, 13329, 5138, 13331, 5144, 13337, 5146, 13339,
    5140, 13333, 5142, 13335, 5148, 13341, 5150, 13343,
    5152, 13345, 5154, 13347, 5160, 13353, 5162, 13355,
    5156, 13349, 5158, 13351, 5164, 13357, 5166, 13359,
    5168, 13361, 5170, 13363, 5176, 13369, 5178, 13371,
    5172, 13365, 5174, 13367, 5180, 13373, 5182, 13375]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row11 : Fin 64 → ℕ :=
  ![4416, 4478, 12669, 12611, 12663, 12617, 4426, 4468,
    4475, 4421, 12614, 12664, 12620, 12658, 4465, 4431,
    12655, 12625, 4434, 4460, 4440, 4454, 12645, 12635,
    12628, 12650, 4457, 4439, 4451, 4445, 12638, 12640,
    12639, 12641, 4450, 4444, 4456, 4438, 12629, 12651,
    12644, 12634, 4441, 4455, 4435, 4461, 12654, 12624,
    4464, 4430, 12621, 12659, 12615, 12665, 4474, 4420,
    4427, 4469, 12662, 12616, 12668, 12610, 4417, 4479]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row12 : Fin 64 → ℕ :=
  ![4480, 12734, 4541, 12675, 12727, 4489, 12682, 4532,
    4539, 12677, 4486, 12728, 12684, 4530, 12721, 4495,
    4527, 12689, 4498, 12716, 12696, 4518, 12709, 4507,
    4500, 12714, 4521, 12695, 12707, 4509, 12702, 4512,
    4511, 12705, 4514, 12700, 12712, 4502, 12693, 4523,
    4516, 12698, 4505, 12711, 12691, 4525, 12718, 4496,
    4528, 12686, 4493, 12723, 12679, 4537, 12730, 4484,
    4491, 12725, 4534, 12680, 12732, 4482, 12673, 4543]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row13 : Fin 64 → ℕ :=
  ![4288, 4350, 12541, 12483, 4343, 4297, 12490, 12532,
    12539, 12485, 4294, 4344, 12492, 12530, 4337, 4303,
    12527, 12497, 4306, 4332, 12504, 12518, 4325, 4315,
    4308, 4330, 12521, 12503, 4323, 4317, 12510, 12512,
    12511, 12513, 4322, 4316, 12520, 12502, 4309, 4331,
    4324, 4314, 12505, 12519, 4307, 4333, 12526, 12496,
    4336, 4302, 12493, 12531, 4295, 4345, 12538, 12484,
    12491, 12533, 4342, 4296, 12540, 12482, 4289, 4351]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row14 : Fin 64 → ℕ :=
  ![4352, 12606, 4413, 12547, 4407, 12553, 4362, 12596,
    12603, 4357, 12550, 4408, 12556, 4402, 12593, 4367,
    4399, 12561, 4370, 12588, 4376, 12582, 4389, 12571,
    12564, 4394, 12585, 4375, 12579, 4381, 12574, 4384,
    4383, 12577, 4386, 12572, 4392, 12566, 4373, 12587,
    12580, 4378, 12569, 4391, 12563, 4397, 12590, 4368,
    4400, 12558, 4365, 12595, 4359, 12601, 4410, 12548,
    12555, 4405, 12598, 4360, 12604, 4354, 12545, 4415]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row15 : Fin 64 → ℕ :=
  ![4672, 12865, 4674, 12867, 12872, 4681, 12874, 4683,
    12868, 4677, 12870, 4679, 4684, 12877, 4686, 12879,
    4688, 12881, 4690, 12883, 12888, 4697, 12890, 4699,
    12884, 4693, 12886, 4695, 4700, 12893, 4702, 12895,
    4704, 12897, 4706, 12899, 12904, 4713, 12906, 4715,
    12900, 4709, 12902, 4711, 4716, 12909, 4718, 12911,
    4720, 12913, 4722, 12915, 12920, 4729, 12922, 4731,
    12916, 4725, 12918, 4727, 4732, 12925, 4734, 12927]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row16 : Fin 64 → ℕ :=
  ![4736, 12929, 4738, 12931, 4744, 12937, 4746, 12939,
    4740, 12933, 4742, 12935, 4748, 12941, 4750, 12943,
    4752, 12945, 4754, 12947, 4760, 12953, 4762, 12955,
    4756, 12949, 4758, 12951, 4764, 12957, 4766, 12959,
    4768, 12961, 4770, 12963, 4776, 12969, 4778, 12971,
    4772, 12965, 4774, 12967, 4780, 12973, 4782, 12975,
    4784, 12977, 4786, 12979, 4792, 12985, 4794, 12987,
    4788, 12981, 4790, 12983, 4796, 12989, 4798, 12991]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row17 : Fin 64 → ℕ :=
  ![4544, 12737, 4546, 12739, 12744, 4553, 12746, 4555,
    12740, 4549, 12742, 4551, 4556, 12749, 4558, 12751,
    4560, 12753, 4562, 12755, 12760, 4569, 12762, 4571,
    12756, 4565, 12758, 4567, 4572, 12765, 4574, 12767,
    4576, 12769, 4578, 12771, 12776, 4585, 12778, 4587,
    12772, 4581, 12774, 4583, 4588, 12781, 4590, 12783,
    4592, 12785, 4594, 12787, 12792, 4601, 12794, 4603,
    12788, 4597, 12790, 4599, 4604, 12797, 4606, 12799]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row18 : Fin 64 → ℕ :=
  ![4608, 12801, 4610, 12803, 4616, 12809, 4618, 12811,
    4612, 12805, 4614, 12807, 4620, 12813, 4622, 12815,
    4624, 12817, 4626, 12819, 4632, 12825, 4634, 12827,
    4628, 12821, 4630, 12823, 4636, 12829, 4638, 12831,
    4640, 12833, 4642, 12835, 4648, 12841, 4650, 12843,
    4644, 12837, 4646, 12839, 4652, 12845, 4654, 12847,
    4656, 12849, 4658, 12851, 4664, 12857, 4666, 12859,
    4660, 12853, 4662, 12855, 4668, 12861, 4670, 12863]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row19 : Fin 64 → ℕ :=
  ![5312, 5316, 13512, 13516, 5313, 5317, 13513, 13517,
    13506, 13510, 5322, 5326, 13507, 13511, 5323, 5327,
    5328, 5332, 13528, 13532, 5329, 5333, 13529, 13533,
    13522, 13526, 5338, 5342, 13523, 13527, 5339, 5343,
    5344, 5348, 13544, 13548, 5345, 5349, 13545, 13549,
    13538, 13542, 5354, 5358, 13539, 13543, 5355, 5359,
    5360, 5364, 13560, 13564, 5361, 5365, 13561, 13565,
    13554, 13558, 5370, 5374, 13555, 13559, 5371, 5375]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row20 : Fin 64 → ℕ :=
  ![5376, 5437, 5438, 5379, 13623, 13578, 13577, 13620,
    13627, 13574, 13573, 13624, 5388, 5425, 5426, 5391,
    13599, 13602, 13601, 13596, 5416, 5397, 5398, 5419,
    5412, 5401, 5402, 5415, 13587, 13614, 13613, 13584,
    13615, 13586, 13585, 13612, 5400, 5413, 5414, 5403,
    5396, 5417, 5418, 5399, 13603, 13598, 13597, 13600,
    5424, 5389, 5390, 5427, 13575, 13626, 13625, 13572,
    13579, 13622, 13621, 13576, 5436, 5377, 5378, 5439]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row21 : Fin 64 → ℕ :=
  ![5824, 5826, 5825, 5827, 5828, 5830, 5829, 5831,
    14024, 14026, 14025, 14027, 14028, 14030, 14029, 14031,
    5840, 5842, 5841, 5843, 5844, 5846, 5845, 5847,
    14040, 14042, 14041, 14043, 14044, 14046, 14045, 14047,
    5856, 5858, 5857, 5859, 5860, 5862, 5861, 5863,
    14056, 14058, 14057, 14059, 14060, 14062, 14061, 14063,
    5872, 5874, 5873, 5875, 5876, 5878, 5877, 5879,
    14072, 14074, 14073, 14075, 14076, 14078, 14077, 14079]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row22 : Fin 64 → ℕ :=
  ![5888, 14082, 14081, 5891, 5892, 14086, 14085, 5895,
    14088, 5898, 5897, 14091, 14092, 5902, 5901, 14095,
    5904, 14098, 14097, 5907, 5908, 14102, 14101, 5911,
    14104, 5914, 5913, 14107, 14108, 5918, 5917, 14111,
    5920, 14114, 14113, 5923, 5924, 14118, 14117, 5927,
    14120, 5930, 5929, 14123, 14124, 5934, 5933, 14127,
    5936, 14130, 14129, 5939, 5940, 14134, 14133, 5943,
    14136, 5946, 5945, 14139, 14140, 5950, 5949, 14143]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row23 : Fin 64 → ℕ :=
  ![5696, 5698, 5697, 5699, 5700, 5702, 5701, 5703,
    13896, 13898, 13897, 13899, 13900, 13902, 13901, 13903,
    5712, 5714, 5713, 5715, 5716, 5718, 5717, 5719,
    13912, 13914, 13913, 13915, 13916, 13918, 13917, 13919,
    5728, 5730, 5729, 5731, 5732, 5734, 5733, 5735,
    13928, 13930, 13929, 13931, 13932, 13934, 13933, 13935,
    5744, 5746, 5745, 5747, 5748, 5750, 5749, 5751,
    13944, 13946, 13945, 13947, 13948, 13950, 13949, 13951]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row24 : Fin 64 → ℕ :=
  ![5760, 13954, 13953, 5763, 5764, 13958, 13957, 5767,
    13960, 5770, 5769, 13963, 13964, 5774, 5773, 13967,
    5776, 13970, 13969, 5779, 5780, 13974, 13973, 5783,
    13976, 5786, 5785, 13979, 13980, 5790, 5789, 13983,
    5792, 13986, 13985, 5795, 5796, 13990, 13989, 5799,
    13992, 5802, 5801, 13995, 13996, 5806, 5805, 13999,
    5808, 14002, 14001, 5811, 5812, 14006, 14005, 5815,
    14008, 5818, 5817, 14011, 14012, 5822, 5821, 14015]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row25 : Fin 64 → ℕ :=
  ![5568, 5570, 5569, 5571, 5572, 5574, 5573, 5575,
    13768, 13770, 13769, 13771, 13772, 13774, 13773, 13775,
    5584, 5586, 5585, 5587, 5588, 5590, 5589, 5591,
    13784, 13786, 13785, 13787, 13788, 13790, 13789, 13791,
    5600, 5602, 5601, 5603, 5604, 5606, 5605, 5607,
    13800, 13802, 13801, 13803, 13804, 13806, 13805, 13807,
    5616, 5618, 5617, 5619, 5620, 5622, 5621, 5623,
    13816, 13818, 13817, 13819, 13820, 13822, 13821, 13823]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row26 : Fin 64 → ℕ :=
  ![5632, 13826, 13825, 5635, 5636, 13830, 13829, 5639,
    13832, 5642, 5641, 13835, 13836, 5646, 5645, 13839,
    5648, 13842, 13841, 5651, 5652, 13846, 13845, 5655,
    13848, 5658, 5657, 13851, 13852, 5662, 5661, 13855,
    5664, 13858, 13857, 5667, 5668, 13862, 13861, 5671,
    13864, 5674, 5673, 13867, 13868, 5678, 5677, 13871,
    5680, 13874, 13873, 5683, 5684, 13878, 13877, 5687,
    13880, 5690, 5689, 13883, 13884, 5694, 5693, 13887]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row27 : Fin 64 → ℕ :=
  ![5440, 5442, 5441, 5443, 5444, 5446, 5445, 5447,
    13640, 13642, 13641, 13643, 13644, 13646, 13645, 13647,
    5456, 5458, 5457, 5459, 5460, 5462, 5461, 5463,
    13656, 13658, 13657, 13659, 13660, 13662, 13661, 13663,
    5472, 5474, 5473, 5475, 5476, 5478, 5477, 5479,
    13672, 13674, 13673, 13675, 13676, 13678, 13677, 13679,
    5488, 5490, 5489, 5491, 5492, 5494, 5493, 5495,
    13688, 13690, 13689, 13691, 13692, 13694, 13693, 13695]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row28 : Fin 64 → ℕ :=
  ![5504, 13698, 13697, 5507, 5508, 13702, 13701, 5511,
    13704, 5514, 5513, 13707, 13708, 5518, 5517, 13711,
    5520, 13714, 13713, 5523, 5524, 13718, 13717, 5527,
    13720, 5530, 5529, 13723, 13724, 5534, 5533, 13727,
    5536, 13730, 13729, 5539, 5540, 13734, 13733, 5543,
    13736, 5546, 5545, 13739, 13740, 5550, 5549, 13743,
    5552, 13746, 13745, 5555, 5556, 13750, 13749, 5559,
    13752, 5562, 5561, 13755, 13756, 5566, 5565, 13759]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row29 : Fin 64 → ℕ :=
  ![5952, 14206, 14205, 5955, 14203, 5957, 5958, 14200,
    14199, 5961, 5962, 14196, 5964, 14194, 14193, 5967,
    14175, 5985, 5986, 14172, 5988, 14170, 14169, 5991,
    5992, 14166, 14165, 5995, 14163, 5997, 5998, 14160,
    14191, 5969, 5970, 14188, 5972, 14186, 14185, 5975,
    5976, 14182, 14181, 5979, 14179, 5981, 5982, 14176,
    6000, 14158, 14157, 6003, 14155, 6005, 6006, 14152,
    14151, 6009, 6010, 14148, 6012, 14146, 14145, 6015]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row30 : Fin 64 → ℕ :=
  ![6016, 14226, 14225, 6019, 6040, 14218, 14217, 6043,
    6036, 14214, 14213, 6039, 6028, 14238, 14237, 6031,
    6032, 14210, 14209, 6035, 6024, 14234, 14233, 6027,
    6020, 14230, 14229, 6023, 6044, 14222, 14221, 6047,
    14255, 6077, 6078, 14252, 14263, 6053, 6054, 14260,
    14267, 6057, 6058, 14264, 14243, 6065, 6066, 14240,
    14271, 6061, 6062, 14268, 14247, 6069, 6070, 14244,
    14251, 6073, 6074, 14248, 14259, 6049, 6050, 14256]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row31 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14327, 6090, 6089, 14324,
    14331, 6086, 6085, 14328, 0, 0, 0, 0,
    0, 0, 0, 0, 14312, 6101, 6102, 14315,
    14308, 6105, 6106, 14311, 0, 0, 0, 0,
    0, 0, 0, 0, 14296, 6117, 6118, 14299,
    14292, 6121, 6122, 14295, 0, 0, 0, 0,
    0, 0, 0, 0, 14279, 6138, 6137, 14276,
    14283, 6134, 6133, 14280, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row32 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14327, 6090, 6089, 14324,
    14331, 6086, 6085, 14328, 0, 0, 0, 0,
    0, 0, 0, 0, 14312, 6101, 6102, 14315,
    14308, 6105, 6106, 14311, 0, 0, 0, 0,
    0, 0, 0, 0, 14296, 6117, 6118, 14299,
    14292, 6121, 6122, 14295, 0, 0, 0, 0,
    0, 0, 0, 0, 14279, 6138, 6137, 14276,
    14283, 6134, 6133, 14280, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row33 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7752, 15945, 7754, 15947,
    7748, 15941, 7750, 15943, 0, 0, 0, 0,
    0, 0, 0, 0, 7768, 15961, 7770, 15963,
    7764, 15957, 7766, 15959, 0, 0, 0, 0,
    0, 0, 0, 0, 7784, 15977, 7786, 15979,
    7780, 15973, 7782, 15975, 0, 0, 0, 0,
    0, 0, 0, 0, 7800, 15993, 7802, 15995,
    7796, 15989, 7798, 15991, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row34 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7752, 15945, 7754, 15947,
    7748, 15941, 7750, 15943, 0, 0, 0, 0,
    0, 0, 0, 0, 7768, 15961, 7770, 15963,
    7764, 15957, 7766, 15959, 0, 0, 0, 0,
    0, 0, 0, 0, 7784, 15977, 7786, 15979,
    7780, 15973, 7782, 15975, 0, 0, 0, 0,
    0, 0, 0, 0, 7800, 15993, 7802, 15995,
    7796, 15989, 7798, 15991, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row35 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7880, 16073, 7882, 16075,
    7876, 16069, 7878, 16071, 0, 0, 0, 0,
    0, 0, 0, 0, 7896, 16089, 7898, 16091,
    7892, 16085, 7894, 16087, 0, 0, 0, 0,
    0, 0, 0, 0, 7912, 16105, 7914, 16107,
    7908, 16101, 7910, 16103, 0, 0, 0, 0,
    0, 0, 0, 0, 7928, 16121, 7930, 16123,
    7924, 16117, 7926, 16119, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row36 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7880, 16073, 7882, 16075,
    7876, 16069, 7878, 16071, 0, 0, 0, 0,
    0, 0, 0, 0, 7896, 16089, 7898, 16091,
    7892, 16085, 7894, 16087, 0, 0, 0, 0,
    0, 0, 0, 0, 7912, 16105, 7914, 16107,
    7908, 16101, 7910, 16103, 0, 0, 0, 0,
    0, 0, 0, 0, 7928, 16121, 7930, 16123,
    7924, 16117, 7926, 16119, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row37 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6519, 6474, 6473, 6516,
    6523, 6470, 6469, 6520, 0, 0, 0, 0,
    0, 0, 0, 0, 6504, 6485, 6486, 6507,
    6500, 6489, 6490, 6503, 0, 0, 0, 0,
    0, 0, 0, 0, 6488, 6501, 6502, 6491,
    6484, 6505, 6506, 6487, 0, 0, 0, 0,
    0, 0, 0, 0, 6471, 6522, 6521, 6468,
    6475, 6518, 6517, 6472, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row38 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6519, 6474, 6473, 6516,
    6523, 6470, 6469, 6520, 0, 0, 0, 0,
    0, 0, 0, 0, 6504, 6485, 6486, 6507,
    6500, 6489, 6490, 6503, 0, 0, 0, 0,
    0, 0, 0, 0, 6488, 6501, 6502, 6491,
    6484, 6505, 6506, 6487, 0, 0, 0, 0,
    0, 0, 0, 0, 6471, 6522, 6521, 6468,
    6475, 6518, 6517, 6472, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row39 : Fin 64 → ℕ :=
  ![0, 15170, 15169, 0, 0, 15178, 15177, 0,
    0, 6982, 6981, 0, 0, 6990, 6989, 0,
    0, 15186, 15185, 0, 0, 15194, 15193, 0,
    0, 6998, 6997, 0, 0, 7006, 7005, 0,
    0, 15202, 15201, 0, 0, 15210, 15209, 0,
    0, 7014, 7013, 0, 0, 7022, 7021, 0,
    0, 15218, 15217, 0, 0, 15226, 15225, 0,
    0, 7030, 7029, 0, 0, 7038, 7037, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row40 : Fin 64 → ℕ :=
  ![0, 15170, 15169, 0, 0, 15178, 15177, 0,
    0, 6982, 6981, 0, 0, 6990, 6989, 0,
    0, 15186, 15185, 0, 0, 15194, 15193, 0,
    0, 6998, 6997, 0, 0, 7006, 7005, 0,
    0, 15202, 15201, 0, 0, 15210, 15209, 0,
    0, 7014, 7013, 0, 0, 7022, 7021, 0,
    0, 15218, 15217, 0, 0, 15226, 15225, 0,
    0, 7030, 7029, 0, 0, 7038, 7037, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row41 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7368, 15561, 7370, 15563,
    7364, 15557, 7366, 15559, 0, 0, 0, 0,
    0, 0, 0, 0, 7384, 15577, 7386, 15579,
    7380, 15573, 7382, 15575, 0, 0, 0, 0,
    0, 0, 0, 0, 15592, 7401, 15594, 7403,
    15588, 7397, 15590, 7399, 0, 0, 0, 0,
    0, 0, 0, 0, 15608, 7417, 15610, 7419,
    15604, 7413, 15606, 7415, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row42 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7368, 15561, 7370, 15563,
    7364, 15557, 7366, 15559, 0, 0, 0, 0,
    0, 0, 0, 0, 7384, 15577, 7386, 15579,
    7380, 15573, 7382, 15575, 0, 0, 0, 0,
    0, 0, 0, 0, 15592, 7401, 15594, 7403,
    15588, 7397, 15590, 7399, 0, 0, 0, 0,
    0, 0, 0, 0, 15608, 7417, 15610, 7419,
    15604, 7413, 15606, 7415, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row43 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7240, 15433, 7242, 15435,
    7236, 15429, 7238, 15431, 0, 0, 0, 0,
    0, 0, 0, 0, 7256, 15449, 7258, 15451,
    7252, 15445, 7254, 15447, 0, 0, 0, 0,
    0, 0, 0, 0, 15464, 7273, 15466, 7275,
    15460, 7269, 15462, 7271, 0, 0, 0, 0,
    0, 0, 0, 0, 15480, 7289, 15482, 7291,
    15476, 7285, 15478, 7287, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row44 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7240, 15433, 7242, 15435,
    7236, 15429, 7238, 15431, 0, 0, 0, 0,
    0, 0, 0, 0, 7256, 15449, 7258, 15451,
    7252, 15445, 7254, 15447, 0, 0, 0, 0,
    0, 0, 0, 0, 15464, 7273, 15466, 7275,
    15460, 7269, 15462, 7271, 0, 0, 0, 0,
    0, 0, 0, 0, 15480, 7289, 15482, 7291,
    15476, 7285, 15478, 7287, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row45 : Fin 64 → ℕ :=
  ![0, 14786, 14785, 0, 0, 6602, 6601, 0,
    0, 14790, 14789, 0, 0, 6606, 6605, 0,
    0, 14802, 14801, 0, 0, 6618, 6617, 0,
    0, 14806, 14805, 0, 0, 6622, 6621, 0,
    0, 14818, 14817, 0, 0, 6634, 6633, 0,
    0, 14822, 14821, 0, 0, 6638, 6637, 0,
    0, 14834, 14833, 0, 0, 6650, 6649, 0,
    0, 14838, 14837, 0, 0, 6654, 6653, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row46 : Fin 64 → ℕ :=
  ![0, 14786, 14785, 0, 0, 6602, 6601, 0,
    0, 14790, 14789, 0, 0, 6606, 6605, 0,
    0, 14802, 14801, 0, 0, 6618, 6617, 0,
    0, 14806, 14805, 0, 0, 6622, 6621, 0,
    0, 14818, 14817, 0, 0, 6634, 6633, 0,
    0, 14822, 14821, 0, 0, 6638, 6637, 0,
    0, 14834, 14833, 0, 0, 6650, 6649, 0,
    0, 14838, 14837, 0, 0, 6654, 6653, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row47 : Fin 64 → ℕ :=
  ![0, 15682, 15681, 0, 0, 7498, 7497, 0,
    0, 15686, 15685, 0, 0, 7502, 7501, 0,
    0, 15698, 15697, 0, 0, 7514, 7513, 0,
    0, 15702, 15701, 0, 0, 7518, 7517, 0,
    0, 15714, 15713, 0, 0, 7530, 7529, 0,
    0, 15718, 15717, 0, 0, 7534, 7533, 0,
    0, 15730, 15729, 0, 0, 7546, 7545, 0,
    0, 15734, 15733, 0, 0, 7550, 7549, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row48 : Fin 64 → ℕ :=
  ![0, 15682, 15681, 0, 0, 7498, 7497, 0,
    0, 15686, 15685, 0, 0, 7502, 7501, 0,
    0, 15698, 15697, 0, 0, 7514, 7513, 0,
    0, 15702, 15701, 0, 0, 7518, 7517, 0,
    0, 15714, 15713, 0, 0, 7530, 7529, 0,
    0, 15718, 15717, 0, 0, 7534, 7533, 0,
    0, 15730, 15729, 0, 0, 7546, 7545, 0,
    0, 15734, 15733, 0, 0, 7550, 7549, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row49 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6856, 15049, 6858, 15051,
    6852, 15045, 6854, 15047, 0, 0, 0, 0,
    0, 0, 0, 0, 6872, 15065, 6874, 15067,
    6868, 15061, 6870, 15063, 0, 0, 0, 0,
    0, 0, 0, 0, 15080, 6889, 15082, 6891,
    15076, 6885, 15078, 6887, 0, 0, 0, 0,
    0, 0, 0, 0, 15096, 6905, 15098, 6907,
    15092, 6901, 15094, 6903, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row50 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6856, 15049, 6858, 15051,
    6852, 15045, 6854, 15047, 0, 0, 0, 0,
    0, 0, 0, 0, 6872, 15065, 6874, 15067,
    6868, 15061, 6870, 15063, 0, 0, 0, 0,
    0, 0, 0, 0, 15080, 6889, 15082, 6891,
    15076, 6885, 15078, 6887, 0, 0, 0, 0,
    0, 0, 0, 0, 15096, 6905, 15098, 6907,
    15092, 6901, 15094, 6903, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row51 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6728, 14921, 6730, 14923,
    6724, 14917, 6726, 14919, 0, 0, 0, 0,
    0, 0, 0, 0, 6744, 14937, 6746, 14939,
    6740, 14933, 6742, 14935, 0, 0, 0, 0,
    0, 0, 0, 0, 14952, 6761, 14954, 6763,
    14948, 6757, 14950, 6759, 0, 0, 0, 0,
    0, 0, 0, 0, 14968, 6777, 14970, 6779,
    14964, 6773, 14966, 6775, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row52 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6728, 14921, 6730, 14923,
    6724, 14917, 6726, 14919, 0, 0, 0, 0,
    0, 0, 0, 0, 6744, 14937, 6746, 14939,
    6740, 14933, 6742, 14935, 0, 0, 0, 0,
    0, 0, 0, 0, 14952, 6761, 14954, 6763,
    14948, 6757, 14950, 6759, 0, 0, 0, 0,
    0, 0, 0, 0, 14968, 6777, 14970, 6779,
    14964, 6773, 14966, 6775, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row53 : Fin 64 → ℕ :=
  ![0, 15298, 15297, 0, 0, 15306, 15305, 0,
    0, 7110, 7109, 0, 0, 7118, 7117, 0,
    0, 15314, 15313, 0, 0, 15322, 15321, 0,
    0, 7126, 7125, 0, 0, 7134, 7133, 0,
    0, 15330, 15329, 0, 0, 15338, 15337, 0,
    0, 7142, 7141, 0, 0, 7150, 7149, 0,
    0, 15346, 15345, 0, 0, 15354, 15353, 0,
    0, 7158, 7157, 0, 0, 7166, 7165, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row54 : Fin 64 → ℕ :=
  ![0, 15298, 15297, 0, 0, 15306, 15305, 0,
    0, 7110, 7109, 0, 0, 7118, 7117, 0,
    0, 15314, 15313, 0, 0, 15322, 15321, 0,
    0, 7126, 7125, 0, 0, 7134, 7133, 0,
    0, 15330, 15329, 0, 0, 15338, 15337, 0,
    0, 7142, 7141, 0, 0, 7150, 7149, 0,
    0, 15346, 15345, 0, 0, 15354, 15353, 0,
    0, 7158, 7157, 0, 0, 7166, 7165, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row55 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7671, 15818, 15817, 7668,
    7675, 15814, 15813, 7672, 0, 0, 0, 0,
    0, 0, 0, 0, 15848, 7637, 7638, 15851,
    15844, 7641, 7642, 15847, 0, 0, 0, 0,
    0, 0, 0, 0, 15832, 7653, 7654, 15835,
    15828, 7657, 7658, 15831, 0, 0, 0, 0,
    0, 0, 0, 0, 7623, 15866, 15865, 7620,
    7627, 15862, 15861, 7624, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row56 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7671, 15818, 15817, 7668,
    7675, 15814, 15813, 7672, 0, 0, 0, 0,
    0, 0, 0, 0, 15848, 7637, 7638, 15851,
    15844, 7641, 7642, 15847, 0, 0, 0, 0,
    0, 0, 0, 0, 15832, 7653, 7654, 15835,
    15828, 7657, 7658, 15831, 0, 0, 0, 0,
    0, 0, 0, 0, 7623, 15866, 15865, 7620,
    7627, 15862, 15861, 7624, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row57 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6216, 14409, 6218, 14411,
    6212, 14405, 6214, 14407, 0, 0, 0, 0,
    0, 0, 0, 0, 6232, 14425, 6234, 14427,
    6228, 14421, 6230, 14423, 0, 0, 0, 0,
    0, 0, 0, 0, 6248, 14441, 6250, 14443,
    6244, 14437, 6246, 14439, 0, 0, 0, 0,
    0, 0, 0, 0, 6264, 14457, 6266, 14459,
    6260, 14453, 6262, 14455, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row58 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6216, 14409, 6218, 14411,
    6212, 14405, 6214, 14407, 0, 0, 0, 0,
    0, 0, 0, 0, 6232, 14425, 6234, 14427,
    6228, 14421, 6230, 14423, 0, 0, 0, 0,
    0, 0, 0, 0, 6248, 14441, 6250, 14443,
    6244, 14437, 6246, 14439, 0, 0, 0, 0,
    0, 0, 0, 0, 6264, 14457, 6266, 14459,
    6260, 14453, 6262, 14455, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row59 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6344, 14537, 6346, 14539,
    6340, 14533, 6342, 14535, 0, 0, 0, 0,
    0, 0, 0, 0, 6360, 14553, 6362, 14555,
    6356, 14549, 6358, 14551, 0, 0, 0, 0,
    0, 0, 0, 0, 6376, 14569, 6378, 14571,
    6372, 14565, 6374, 14567, 0, 0, 0, 0,
    0, 0, 0, 0, 6392, 14585, 6394, 14587,
    6388, 14581, 6390, 14583, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row60 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6344, 14537, 6346, 14539,
    6340, 14533, 6342, 14535, 0, 0, 0, 0,
    0, 0, 0, 0, 6360, 14553, 6362, 14555,
    6356, 14549, 6358, 14551, 0, 0, 0, 0,
    0, 0, 0, 0, 6376, 14569, 6378, 14571,
    6372, 14565, 6374, 14567, 0, 0, 0, 0,
    0, 0, 0, 0, 6392, 14585, 6394, 14587,
    6388, 14581, 6390, 14583, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row61 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 16247, 16202, 16201, 16244,
    16251, 16198, 16197, 16248, 0, 0, 0, 0,
    0, 0, 0, 0, 8040, 8021, 8022, 8043,
    8036, 8025, 8026, 8039, 0, 0, 0, 0,
    0, 0, 0, 0, 8024, 8037, 8038, 8027,
    8020, 8041, 8042, 8023, 0, 0, 0, 0,
    0, 0, 0, 0, 16199, 16250, 16249, 16196,
    16203, 16246, 16245, 16200, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord3Row62 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 16247, 16202, 16201, 16244,
    16251, 16198, 16197, 16248, 0, 0, 0, 0,
    0, 0, 0, 0, 8040, 8021, 8022, 8043,
    8036, 8025, 8026, 8039, 0, 0, 0, 0,
    0, 0, 0, 0, 8024, 8037, 8038, 8027,
    8020, 8041, 8042, 8023, 0, 0, 0, 0,
    0, 0, 0, 0, 16199, 16250, 16249, 16196,
    16203, 16246, 16245, 16200, 0, 0, 0, 0]

/-- Literal candidate octad target addresses, with the target central phase retained. -/
def generatedFourthMonomialShortOctadTargets3 : Fin 63 → Fin 64 → ℕ :=
  ![
    generatedFourthMonomialOctadWord3Row0,
    generatedFourthMonomialOctadWord3Row1,
    generatedFourthMonomialOctadWord3Row2,
    generatedFourthMonomialOctadWord3Row3,
    generatedFourthMonomialOctadWord3Row4,
    generatedFourthMonomialOctadWord3Row5,
    generatedFourthMonomialOctadWord3Row6,
    generatedFourthMonomialOctadWord3Row7,
    generatedFourthMonomialOctadWord3Row8,
    generatedFourthMonomialOctadWord3Row9,
    generatedFourthMonomialOctadWord3Row10,
    generatedFourthMonomialOctadWord3Row11,
    generatedFourthMonomialOctadWord3Row12,
    generatedFourthMonomialOctadWord3Row13,
    generatedFourthMonomialOctadWord3Row14,
    generatedFourthMonomialOctadWord3Row15,
    generatedFourthMonomialOctadWord3Row16,
    generatedFourthMonomialOctadWord3Row17,
    generatedFourthMonomialOctadWord3Row18,
    generatedFourthMonomialOctadWord3Row19,
    generatedFourthMonomialOctadWord3Row20,
    generatedFourthMonomialOctadWord3Row21,
    generatedFourthMonomialOctadWord3Row22,
    generatedFourthMonomialOctadWord3Row23,
    generatedFourthMonomialOctadWord3Row24,
    generatedFourthMonomialOctadWord3Row25,
    generatedFourthMonomialOctadWord3Row26,
    generatedFourthMonomialOctadWord3Row27,
    generatedFourthMonomialOctadWord3Row28,
    generatedFourthMonomialOctadWord3Row29,
    generatedFourthMonomialOctadWord3Row30,
    generatedFourthMonomialOctadWord3Row31,
    generatedFourthMonomialOctadWord3Row32,
    generatedFourthMonomialOctadWord3Row33,
    generatedFourthMonomialOctadWord3Row34,
    generatedFourthMonomialOctadWord3Row35,
    generatedFourthMonomialOctadWord3Row36,
    generatedFourthMonomialOctadWord3Row37,
    generatedFourthMonomialOctadWord3Row38,
    generatedFourthMonomialOctadWord3Row39,
    generatedFourthMonomialOctadWord3Row40,
    generatedFourthMonomialOctadWord3Row41,
    generatedFourthMonomialOctadWord3Row42,
    generatedFourthMonomialOctadWord3Row43,
    generatedFourthMonomialOctadWord3Row44,
    generatedFourthMonomialOctadWord3Row45,
    generatedFourthMonomialOctadWord3Row46,
    generatedFourthMonomialOctadWord3Row47,
    generatedFourthMonomialOctadWord3Row48,
    generatedFourthMonomialOctadWord3Row49,
    generatedFourthMonomialOctadWord3Row50,
    generatedFourthMonomialOctadWord3Row51,
    generatedFourthMonomialOctadWord3Row52,
    generatedFourthMonomialOctadWord3Row53,
    generatedFourthMonomialOctadWord3Row54,
    generatedFourthMonomialOctadWord3Row55,
    generatedFourthMonomialOctadWord3Row56,
    generatedFourthMonomialOctadWord3Row57,
    generatedFourthMonomialOctadWord3Row58,
    generatedFourthMonomialOctadWord3Row59,
    generatedFourthMonomialOctadWord3Row60,
    generatedFourthMonomialOctadWord3Row61,
    generatedFourthMonomialOctadWord3Row62
  ]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row0 : Fin 24 → ℕ :=
  ![0, 48, 8338, 8290, 0, 0, 0, 0,
    0, 0, 0, 0, 8866, 722, 8770, 626,
    8962, 9010, 9058, 9106, 9202, 9154, 1106, 1058]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row1 : Fin 24 → ℕ :=
  ![0, 0, 8336, 8288, 0, 0, 0, 0,
    0, 0, 0, 0, 8864, 720, 8768, 624,
    8960, 9008, 9056, 9104, 9200, 9152, 1104, 1056]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 148, 0, 0, 0, 0,
    0, 0, 0, 0, 678, 8918, 582, 8822,
    774, 822, 870, 918, 1014, 966, 9302, 9254]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 676, 8916, 580, 8820,
    772, 820, 868, 916, 1012, 964, 9300, 9252]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 248, 296, 344,
    8728, 488, 440, 8584, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 298, 346,
    8730, 490, 442, 8586, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 348,
    8732, 492, 444, 8588, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    8734, 494, 446, 8590, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 8740, 8738, 544, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 498, 8688, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 8640, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 8940, 696, 8890,
    796, 844, 892, 940, 1036, 988, 9324, 9276]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 8936, 746,
    8990, 9038, 9086, 9134, 9230, 9182, 1134, 1086]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 8840,
    792, 840, 888, 936, 1032, 984, 9320, 9272]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    8986, 9034, 9082, 9130, 9226, 9178, 1130, 1082]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 848, 896, 944, 1040, 992, 9328, 9280]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 898, 946, 1042, 994, 9330, 9282]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 948, 1044, 996, 9332, 9284]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1046, 998, 9334, 9286]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1048, 9338, 9290]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 9336, 9288]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1148]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign0Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row0 : Fin 24 → ℕ :=
  ![0, 49, 8339, 8291, 0, 0, 0, 0,
    0, 0, 0, 0, 8867, 723, 8771, 627,
    8963, 9011, 9059, 9107, 9203, 9155, 1107, 1059]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row1 : Fin 24 → ℕ :=
  ![0, 0, 8337, 8289, 0, 0, 0, 0,
    0, 0, 0, 0, 8865, 721, 8769, 625,
    8961, 9009, 9057, 9105, 9201, 9153, 1105, 1057]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 149, 0, 0, 0, 0,
    0, 0, 0, 0, 679, 8919, 583, 8823,
    775, 823, 871, 919, 1015, 967, 9303, 9255]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 677, 8917, 581, 8821,
    773, 821, 869, 917, 1013, 965, 9301, 9253]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 249, 297, 345,
    8729, 489, 441, 8585, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 299, 347,
    8731, 491, 443, 8587, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 349,
    8733, 493, 445, 8589, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    8735, 495, 447, 8591, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 8741, 8739, 545, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 499, 8689, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 8641, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 8941, 697, 8891,
    797, 845, 893, 941, 1037, 989, 9325, 9277]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 8937, 747,
    8991, 9039, 9087, 9135, 9231, 9183, 1135, 1087]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 8841,
    793, 841, 889, 937, 1033, 985, 9321, 9273]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    8987, 9035, 9083, 9131, 9227, 9179, 1131, 1083]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 849, 897, 945, 1041, 993, 9329, 9281]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 899, 947, 1043, 995, 9331, 9283]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 949, 1045, 997, 9333, 9285]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1047, 999, 9335, 9287]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1049, 9339, 9291]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 9337, 9289]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1149]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord3Sign1Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- Literal candidate pair target addresses for both original preferred signs. -/
def generatedFourthMonomialShortPairTargets3 : Fin 2 → Fin 24 → Fin 24 → ℕ :=
  ![
    ![generatedFourthMonomialPairWord3Sign0Row0,
    generatedFourthMonomialPairWord3Sign0Row1,
    generatedFourthMonomialPairWord3Sign0Row2,
    generatedFourthMonomialPairWord3Sign0Row3,
    generatedFourthMonomialPairWord3Sign0Row4,
    generatedFourthMonomialPairWord3Sign0Row5,
      generatedFourthMonomialPairWord3Sign0Row6,
    generatedFourthMonomialPairWord3Sign0Row7,
    generatedFourthMonomialPairWord3Sign0Row8,
    generatedFourthMonomialPairWord3Sign0Row9,
    generatedFourthMonomialPairWord3Sign0Row10,
    generatedFourthMonomialPairWord3Sign0Row11,
      generatedFourthMonomialPairWord3Sign0Row12,
    generatedFourthMonomialPairWord3Sign0Row13,
    generatedFourthMonomialPairWord3Sign0Row14,
    generatedFourthMonomialPairWord3Sign0Row15,
    generatedFourthMonomialPairWord3Sign0Row16,
    generatedFourthMonomialPairWord3Sign0Row17,
      generatedFourthMonomialPairWord3Sign0Row18,
    generatedFourthMonomialPairWord3Sign0Row19,
    generatedFourthMonomialPairWord3Sign0Row20,
    generatedFourthMonomialPairWord3Sign0Row21,
    generatedFourthMonomialPairWord3Sign0Row22,
    generatedFourthMonomialPairWord3Sign0Row23],
    ![generatedFourthMonomialPairWord3Sign1Row0,
    generatedFourthMonomialPairWord3Sign1Row1,
    generatedFourthMonomialPairWord3Sign1Row2,
    generatedFourthMonomialPairWord3Sign1Row3,
    generatedFourthMonomialPairWord3Sign1Row4,
    generatedFourthMonomialPairWord3Sign1Row5,
      generatedFourthMonomialPairWord3Sign1Row6,
    generatedFourthMonomialPairWord3Sign1Row7,
    generatedFourthMonomialPairWord3Sign1Row8,
    generatedFourthMonomialPairWord3Sign1Row9,
    generatedFourthMonomialPairWord3Sign1Row10,
    generatedFourthMonomialPairWord3Sign1Row11,
      generatedFourthMonomialPairWord3Sign1Row12,
    generatedFourthMonomialPairWord3Sign1Row13,
    generatedFourthMonomialPairWord3Sign1Row14,
    generatedFourthMonomialPairWord3Sign1Row15,
    generatedFourthMonomialPairWord3Sign1Row16,
    generatedFourthMonomialPairWord3Sign1Row17,
      generatedFourthMonomialPairWord3Sign1Row18,
    generatedFourthMonomialPairWord3Sign1Row19,
    generatedFourthMonomialPairWord3Sign1Row20,
    generatedFourthMonomialPairWord3Sign1Row21,
    generatedFourthMonomialPairWord3Sign1Row22,
    generatedFourthMonomialPairWord3Sign1Row23]
  ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
