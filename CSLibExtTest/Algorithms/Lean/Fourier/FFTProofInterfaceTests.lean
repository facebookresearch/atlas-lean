/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ArrayCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Butterfly
public import CSLibExt.Algorithms.Lean.Fourier.FFT.CanonicalDFT
public import CSLibExt.Algorithms.Lean.Fourier.FFT.CircularCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Convolution
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionArrayCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCharacteristic
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCost
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Correctness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Cost
public import CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Inverse
public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCanonicalDFT
public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCost
public import CSLibExt.Algorithms.Lean.Fourier.FFT.LinearCorrectness
public import CSLibExt.Algorithms.Lean.Fourier.FFT.PaddingCircular
public import CSLibExt.Algorithms.Lean.Fourier.FFT.Polynomial
public import CSLibExt.Algorithms.Lean.Fourier.FFT.PositiveRoundtrip
public import MathlibExt.Analysis.Fourier.VectorDFT
public import MathlibExt.Analysis.Fourier.ZModConvolution

@[expose] public section

-- Every allocated public name must resolve from the production module imports.
#check Cslib.Algorithms.Lean.TimeM.fftSplit
#check Cslib.Algorithms.Lean.TimeM.fftButterfly
#check Cslib.Algorithms.Lean.TimeM.fftButterflies
#check Cslib.Algorithms.Lean.TimeM.fft
#check Cslib.Algorithms.Lean.TimeM.fftArray
#check Cslib.Algorithms.Lean.TimeM.fftArray_eq_none_iff
#check Cslib.Algorithms.Lean.TimeM.fftArray_ret_of_vector
#check Cslib.Algorithms.Lean.TimeM.fftArray_time_of_vector
#check Cslib.Algorithms.Lean.TimeM.fftArray_correct
#check Cslib.Algorithms.Lean.TimeM.fftArray_time_add_one
#check Cslib.Algorithms.Lean.TimeM.fftButterfly_ret_low
#check Cslib.Algorithms.Lean.TimeM.fftButterfly_ret_high
#check Cslib.Algorithms.Lean.TimeM.fftButterfly_ret_other
#check Cslib.Algorithms.Lean.TimeM.fftButterflies_ret
#check Cslib.Algorithms.Lean.TimeM.fft_stdAddChar_neg_one
#check Cslib.Algorithms.Lean.TimeM.fft_stdAddChar_one_normalized
#check Cslib.Algorithms.Lean.TimeM.fftCircular_ret
#check Cslib.Algorithms.Lean.TimeM.fftLinear_ret
#check Cslib.Algorithms.Lean.TimeM.fftCircular_stdAddChar_neg_one
#check Cslib.Algorithms.Lean.TimeM.fftCircular_stdAddChar_one
#check Cslib.Algorithms.Lean.TimeM.fftPointwise
#check Cslib.Algorithms.Lean.TimeM.fftPad
#check Cslib.Algorithms.Lean.TimeM.fftCircular
#check Cslib.Algorithms.Lean.TimeM.fftLinear
#check Cslib.Algorithms.Lean.TimeM.fftCircularArray
#check Cslib.Algorithms.Lean.TimeM.fftLinearArray
#check Cslib.Algorithms.Lean.TimeM.fftCircularArray_ret_of_vector
#check Cslib.Algorithms.Lean.TimeM.fftCircularArray_time_of_vector
#check Cslib.Algorithms.Lean.TimeM.fftCircularArray_time_add_two
#check Cslib.Algorithms.Lean.TimeM.fftCircularArray_size_of_eq_some
#check Cslib.Algorithms.Lean.TimeM.fftLinearArray_ret_of_vector
#check Cslib.Algorithms.Lean.TimeM.fftLinearArray_time_of_vector
#check Cslib.Algorithms.Lean.TimeM.fftLinearArray_time_add_two
#check Cslib.Algorithms.Lean.TimeM.fftLinearArray_size_of_eq_some
#check Cslib.Algorithms.Lean.TimeM.fftPointwise_ret
#check Cslib.Algorithms.Lean.TimeM.fftPad_ret_low
#check Cslib.Algorithms.Lean.TimeM.fftPad_ret_high
#check Cslib.Algorithms.Lean.TimeM.fftCircularArray_eq_none_iff
#check Cslib.Algorithms.Lean.TimeM.fftLinearArray_eq_none_iff
#check Cslib.Algorithms.Lean.TimeM.fftPointwise_time
#check Cslib.Algorithms.Lean.TimeM.fftPad_time
#check Cslib.Algorithms.Lean.TimeM.fftCircular_time_add_two
#check Cslib.Algorithms.Lean.TimeM.fftCircular_time_le
#check Cslib.Algorithms.Lean.TimeM.fftLinear_time_add_two
#check Cslib.Algorithms.Lean.TimeM.fftLinear_time_le
#check Cslib.Algorithms.Lean.TimeM.fftSplit_ret_even
#check Cslib.Algorithms.Lean.TimeM.fftSplit_ret_odd
#check Cslib.Algorithms.Lean.TimeM.fft_ret_zero
#check Cslib.Algorithms.Lean.TimeM.fft_ret_succ_low
#check Cslib.Algorithms.Lean.TimeM.fft_ret_succ_high
#check Cslib.Algorithms.Lean.TimeM.fftSplit_time
#check Cslib.Algorithms.Lean.TimeM.fftButterfly_time
#check Cslib.Algorithms.Lean.TimeM.fftButterflies_time
#check Cslib.Algorithms.Lean.TimeM.fft_time_add_one
#check Cslib.Algorithms.Lean.TimeM.fft_time_add_one_log2
#check Cslib.Algorithms.Lean.TimeM.fft_time_le
#check Cslib.Algorithms.Lean.TimeM.fft_correct
#check Cslib.Algorithms.Lean.TimeM.fftConjugate
#check Cslib.Algorithms.Lean.TimeM.fftScale
#check Cslib.Algorithms.Lean.TimeM.ifft
#check Cslib.Algorithms.Lean.TimeM.ifft_stdAddChar_neg_one
#check Cslib.Algorithms.Lean.TimeM.ifft_stdAddChar_one
#check Cslib.Algorithms.Lean.TimeM.ifft_fft_stdAddChar_neg_one
#check Cslib.Algorithms.Lean.TimeM.fft_ifft_stdAddChar_neg_one
#check Cslib.Algorithms.Lean.TimeM.fft_conjugate_ret
#check Cslib.Algorithms.Lean.TimeM.ifft_ret
#check Cslib.Algorithms.Lean.TimeM.ifft_correct
#check Cslib.Algorithms.Lean.TimeM.fftConjugate_time
#check Cslib.Algorithms.Lean.TimeM.fftScale_time
#check Cslib.Algorithms.Lean.TimeM.ifft_time_add_one
#check Cslib.Algorithms.Lean.TimeM.ifft_time_le
#check Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_neg_one_coeff
#check Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_neg_one_sum
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_fftLinear_stdAddChar_neg_one
#check Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_neg_one_last
#check Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_one_coeff
#check Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_one_sum
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_fftLinear_stdAddChar_one
#check Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_one_last
#check Cslib.Algorithms.Lean.TimeM.fftPad_circular_coeff_eq_polynomial
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_coeff
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_fftPad
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_mul_coeff
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_mul_last
#check Cslib.Algorithms.Lean.TimeM.fftPolynomial_mul_coeff_eq_zero_of_two_mul_le
#check Cslib.Algorithms.Lean.TimeM.ifft_fft_stdAddChar_one
#check Cslib.Algorithms.Lean.TimeM.fft_ifft_stdAddChar_one
#check MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum_stdAddChar_neg_vector
#check MathlibExt.Analysis.Fourier.FastFourierTransformWanted.invDFT_eq_dftSum_stdAddChar_vector
#check MathlibExt.Analysis.Fourier.FastFourierTransformWanted.isPrimitiveRoot_stdAddChar_one
#check MathlibExt.Analysis.Fourier.FastFourierTransformWanted.isPrimitiveRoot_stdAddChar_neg_one
#check MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_one_eq_exp
#check MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_neg_one_eq_exp
#check ZMod.conj_stdAddChar
#check ZMod.invDFT_mul_dft

-- Report actual kernel trust dependencies for this complete public surface.
#print axioms Cslib.Algorithms.Lean.TimeM.fftSplit
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterfly
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterflies
#print axioms Cslib.Algorithms.Lean.TimeM.fft
#print axioms Cslib.Algorithms.Lean.TimeM.fftArray
#print axioms Cslib.Algorithms.Lean.TimeM.fftArray_eq_none_iff
#print axioms Cslib.Algorithms.Lean.TimeM.fftArray_ret_of_vector
#print axioms Cslib.Algorithms.Lean.TimeM.fftArray_time_of_vector
#print axioms Cslib.Algorithms.Lean.TimeM.fftArray_correct
#print axioms Cslib.Algorithms.Lean.TimeM.fftArray_time_add_one
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterfly_ret_low
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterfly_ret_high
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterfly_ret_other
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterflies_ret
#print axioms Cslib.Algorithms.Lean.TimeM.fft_stdAddChar_neg_one
#print axioms Cslib.Algorithms.Lean.TimeM.fft_stdAddChar_one_normalized
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircular_ret
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_ret
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircular_stdAddChar_neg_one
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircular_stdAddChar_one
#print axioms Cslib.Algorithms.Lean.TimeM.fftPointwise
#print axioms Cslib.Algorithms.Lean.TimeM.fftPad
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircular
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircularArray
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinearArray
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircularArray_ret_of_vector
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircularArray_time_of_vector
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircularArray_time_add_two
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircularArray_size_of_eq_some
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinearArray_ret_of_vector
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinearArray_time_of_vector
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinearArray_time_add_two
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinearArray_size_of_eq_some
#print axioms Cslib.Algorithms.Lean.TimeM.fftPointwise_ret
#print axioms Cslib.Algorithms.Lean.TimeM.fftPad_ret_low
#print axioms Cslib.Algorithms.Lean.TimeM.fftPad_ret_high
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircularArray_eq_none_iff
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinearArray_eq_none_iff
#print axioms Cslib.Algorithms.Lean.TimeM.fftPointwise_time
#print axioms Cslib.Algorithms.Lean.TimeM.fftPad_time
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircular_time_add_two
#print axioms Cslib.Algorithms.Lean.TimeM.fftCircular_time_le
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_time_add_two
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_time_le
#print axioms Cslib.Algorithms.Lean.TimeM.fftSplit_ret_even
#print axioms Cslib.Algorithms.Lean.TimeM.fftSplit_ret_odd
#print axioms Cslib.Algorithms.Lean.TimeM.fft_ret_zero
#print axioms Cslib.Algorithms.Lean.TimeM.fft_ret_succ_low
#print axioms Cslib.Algorithms.Lean.TimeM.fft_ret_succ_high
#print axioms Cslib.Algorithms.Lean.TimeM.fftSplit_time
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterfly_time
#print axioms Cslib.Algorithms.Lean.TimeM.fftButterflies_time
#print axioms Cslib.Algorithms.Lean.TimeM.fft_time_add_one
#print axioms Cslib.Algorithms.Lean.TimeM.fft_time_add_one_log2
#print axioms Cslib.Algorithms.Lean.TimeM.fft_time_le
#print axioms Cslib.Algorithms.Lean.TimeM.fft_correct
#print axioms Cslib.Algorithms.Lean.TimeM.fftConjugate
#print axioms Cslib.Algorithms.Lean.TimeM.fftScale
#print axioms Cslib.Algorithms.Lean.TimeM.ifft
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_stdAddChar_neg_one
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_stdAddChar_one
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_fft_stdAddChar_neg_one
#print axioms Cslib.Algorithms.Lean.TimeM.fft_ifft_stdAddChar_neg_one
#print axioms Cslib.Algorithms.Lean.TimeM.fft_conjugate_ret
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_ret
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_correct
#print axioms Cslib.Algorithms.Lean.TimeM.fftConjugate_time
#print axioms Cslib.Algorithms.Lean.TimeM.fftScale_time
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_time_add_one
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_time_le
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_neg_one_coeff
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_neg_one_sum
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_fftLinear_stdAddChar_neg_one
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_neg_one_last
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_one_coeff
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_one_sum
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_fftLinear_stdAddChar_one
#print axioms Cslib.Algorithms.Lean.TimeM.fftLinear_stdAddChar_one_last
#print axioms Cslib.Algorithms.Lean.TimeM.fftPad_circular_coeff_eq_polynomial
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_coeff
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_fftPad
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_mul_coeff
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_mul_last
#print axioms Cslib.Algorithms.Lean.TimeM.fftPolynomial_mul_coeff_eq_zero_of_two_mul_le
#print axioms Cslib.Algorithms.Lean.TimeM.ifft_fft_stdAddChar_one
#print axioms Cslib.Algorithms.Lean.TimeM.fft_ifft_stdAddChar_one
#print axioms MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum_stdAddChar_neg_vector
#print axioms MathlibExt.Analysis.Fourier.FastFourierTransformWanted.invDFT_eq_dftSum_stdAddChar_vector
#print axioms MathlibExt.Analysis.Fourier.FastFourierTransformWanted.isPrimitiveRoot_stdAddChar_one
#print axioms MathlibExt.Analysis.Fourier.FastFourierTransformWanted.isPrimitiveRoot_stdAddChar_neg_one
#print axioms MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_one_eq_exp
#print axioms MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_neg_one_eq_exp
#print axioms ZMod.conj_stdAddChar
#print axioms ZMod.invDFT_mul_dft
