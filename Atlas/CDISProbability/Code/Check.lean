/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib
/-!
# V2: every Mathlib declaration claimed as a bridge exists

One `example := @decl` per declaration named in `targets_annotes.yaml` (ids in comments).
Built as part of `lake build`, so a renamed or removed declaration breaks the build.
Two names from the original brief were wrong and are fixed here (ids 24 and 42).
-/
open MeasureTheory ProbabilityTheory Filter Topology

-- P.I
noncomputable example := @MeasurableSpace                              -- 2
noncomputable example := @IsProbabilityMeasure                         -- 3
noncomputable example := @MeasureTheory.ae                             -- 4
noncomputable example := @prob_compl_eq_one_sub                        -- 5
noncomputable example := @measure_mono                                 -- 5
noncomputable example := @measure_union_add_inter                      -- 5
noncomputable example := @tendsto_measure_iUnion_atTop                 -- 6
noncomputable example := @measure_iUnion_le                            -- 7
noncomputable example := @ProbabilityTheory.cond                       -- 8
noncomputable example := @cond_isProbabilityMeasure                    -- 9
noncomputable example := @cond_mul_eq_inter                            -- 9
noncomputable example := @cond_add_cond_compl_eq                       -- 10 (partiel)
noncomputable example := @cond_eq_inv_mul_cond_mul                     -- 11 (partiel)
noncomputable example := @IndepSet                                     -- 12
noncomputable example := @iIndepSet                                    -- 14
noncomputable example := @MeasurableSpace.map                          -- 15
noncomputable example := @Measure.map                                  -- 15, 20
noncomputable example := @MeasurableSpace.generateFrom                 -- 16
noncomputable example := @borel                                        -- 17
noncomputable example := @borel_eq_generateFrom_Iic                    -- 18 (real a)
noncomputable example := @Real.borel_eq_generateFrom_Iic_rat            -- 18 (rational a)
noncomputable example := @Measurable                                   -- 19
noncomputable example := @Continuous.measurable                        -- 21
noncomputable example := @Measurable.add                               -- 22
noncomputable example := @Measurable.mul                               -- 22
noncomputable example := @measurable_of_tendsto_metrizable             -- 22
noncomputable example := @ProbabilityTheory.cdf                        -- 23
noncomputable example := @Measure.eq_of_cdf                            -- 24 (brief had ext_of_cdf)
noncomputable example := @StieltjesFunction.measure                    -- 25
noncomputable example := @cdf_measure_stieltjesFunction                -- 25
noncomputable example := @HasPDF                                       -- 27, 36
-- P.II
noncomputable example := @pdf.integral_pdf_smul                        -- 29
noncomputable example := @integral_add                                 -- 30
noncomputable example := @integral_mono                                -- 30
noncomputable example := @ProbabilityTheory.variance                   -- 31
noncomputable example := @MemLp.mono_exponent                          -- 32, 61
noncomputable example := @ProbabilityTheory.covariance                 -- 33
noncomputable example := @integral_mul_le_Lp_mul_Lq_of_nonneg          -- 34
noncomputable example := @integral_map                                 -- 35, 37, 48
noncomputable example := @covarianceBilin                              -- 39 (partiel)
noncomputable example := @isPosSemidef_covarianceBilin                 -- 40 (partiel)
noncomputable example := @IndepFun                                     -- 41
noncomputable example := @pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf     -- 42 (brief omitted pdf.)
noncomputable example := @IndepFun.comp                                -- 43
noncomputable example := @IndepFun.covariance_eq_zero                  -- 44
-- P.III
noncomputable example := @integral_prod                                -- 49
noncomputable example := @indepFun_iff_map_prod_eq_prod_map_map        -- 50
noncomputable example := @condDistrib                                  -- 53
noncomputable example := @compProd_map_condDistrib                     -- 53
noncomputable example := @integral_condExp                             -- 58
-- P.IV
noncomputable example := @MemLp                                        -- 46, 47, 60
noncomputable example := @mul_meas_ge_le_integral_of_nonneg            -- 62
noncomputable example := @meas_ge_le_variance_div_sq                   -- 63
noncomputable example := @Measure.infinitePi                           -- 64
noncomputable example := @iIndepFun                                    -- 65
noncomputable example := @iIndepFun.comp                               -- 66
noncomputable example := @indep_iSup_of_disjoint                       -- 66
noncomputable example := @measure_limsup_atTop_eq_zero                 -- 67
noncomputable example := @measure_limsup_eq_one                        -- 67
noncomputable example := @TendstoInMeasure                             -- 68
noncomputable example := @tendstoInMeasure_of_tendsto_ae               -- 69
noncomputable example := @tendstoInMeasure_of_tendsto_eLpNorm          -- 69
noncomputable example := @TendstoInMeasure.exists_seq_tendsto_ae       -- 71
noncomputable example := @strong_law_ae_real                           -- 74
noncomputable example := @TendstoInDistribution                        -- 75
noncomputable example := @TendstoInMeasure.tendstoInDistribution       -- 76
noncomputable example := @tendstoInDistribution_inv_sqrt_mul_sum_sub   -- 79
-- 80 (Cramér-Wold, partial)
noncomputable example := @tendstoInDistribution_iff_tendstoInDistribution_inner
noncomputable example := @charFun                                      -- 81
noncomputable example := @norm_charFun_le_one                          -- 82
noncomputable example := @charFun_zero                                 -- 82
noncomputable example := @charFun_neg                                  -- 82
noncomputable example := @Measure.ext_of_charFun                       -- 84
noncomputable example := @indepFun_iff_charFun_prod                    -- 85
noncomputable example := @IndepFun.charFun_map_add_eq_mul              -- 86
noncomputable example := @iteratedDeriv_charFun                        -- 87
noncomputable example := @IsGaussian                                   -- 88
noncomputable example := @isGaussian_iff_charFun_eq                    -- 89
noncomputable example := @tendstoInDistribution_iff_tendsto_charFun    -- 90
-- P.V
noncomputable example := @pdf.IsUniform                                -- 95
noncomputable example := @HasLaw                                       -- utilisé dans les esquisses
noncomputable example := @gaussianReal                                 -- 98
noncomputable example := @integral_comp_polarCoord_symm                -- 98
